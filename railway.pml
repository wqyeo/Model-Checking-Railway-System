// NOTE: In the buffer/approaching is same status, naming is used interchangably.
#define TRAIN_COUNT 4
#define STATION_COUNT 4

mtype:train_state = {STOPPED, IN_TRANSIT, APPROACHING, READY_TO_DEPART};
mtype:signal_command = {WAIT_APPROACHING, STOP_IN_STATION, DEPART};
mtype:signal_information = {BUFFER_FULL, BUFFER_EMPTY, QUERY_BUFFER};

mtype:train_state trains_state[TRAIN_COUNT];
// ID of Station the train's state is targeted towards.
int trains_station[TRAIN_COUNT];

// On an indexed ID, if the station has a train waiting to enter, will contain the train's ID (-1 otherwise)
int station_approaching_train[STATION_COUNT];
// In an indexed ID, if the station has a train in it, will contain the train's ID (-1 otherwise)
int station_occupied_train[STATION_COUNT];

// Train state, train id
chan train_to_signal[STATION_COUNT] = [2] of {mtype:train_state, int};
// Signal command, signal id
chan signal_to_train[TRAIN_COUNT] = [2] of {mtype:signal_command, int};
// Signal information, signal id, train id (optional)
chan signal_to_signal[STATION_COUNT] = [4] of {mtype:signal_information, int, int};

proctype signal(int id; chan signal_next_station; chan signal_previous_station) {
    printf("Process %d for station %d.\n", _pid, id);

    bool prev_awaiting_empty_buffer = false;
    int prev_station_leaving_train_id = -1;

    do :: true ->
        // Assigned when recieving from channels...
        mtype:train_state sender_train_state;
        int sender_train_id;

        mtype:signal_information sender_data;
        int sender_signal_id;
        int sender_signal_train_id;

        if 
        // Recieve and handle incoming train messages.
        :: nempty(train_to_signal[id]) ->
            train_to_signal[id] ? sender_train_state, sender_train_id;

            if
            :: sender_train_state == READY_TO_DEPART ->
                printf("Station %d got depart signal from Train %d.\n", id, sender_train_id);
                printf("Station %d querying next station for buffer info.\n", id, sender_train_id);
                signal_next_station ! QUERY_BUFFER, id, sender_train_id;
            // Nothing in station to block approaching train, send to station..
            :: sender_train_state == APPROACHING && station_occupied_train[id] == -1 ->
                station_occupied_train[id] = sender_train_id;
                if 
                :: station_approaching_train[id] == sender_train_id ->
                    station_approaching_train[id] = -1;
                :: else ->
                    skip;
                fi

                printf("Station %d commanding Train %d to stop in station.\n", id, sender_train_id);
                signal_to_train[sender_train_id] ! STOP_IN_STATION, id;
            :: else ->
                skip;
            fi
        // Recieve and handle incoming signal messages.
        :: nempty(signal_to_signal[id]) ->
            signal_to_signal[id] ? sender_data, sender_signal_id, sender_signal_train_id;

            if
            :: sender_data == QUERY_BUFFER ->
                atomic {
                    printf("Station %d got buffer info request from Station %d for Train %d.\n", id, sender_signal_id, sender_signal_train_id);
                    if
                    :: station_approaching_train[id] != -1 && station_approaching_train[id] != sender_signal_train_id ->
                        prev_awaiting_empty_buffer = true;
                        prev_station_leaving_train_id = sender_signal_train_id;
                        printf("Station %d BUFFER_FULL for Station %d for Train %d. (Occupied by %d)\n", id, sender_signal_id, sender_signal_train_id, station_approaching_train[id]);
                        signal_to_signal[sender_signal_id] ! BUFFER_FULL, id, sender_signal_train_id;
                    :: else ->
                        // Since we know the query is for allowing trains to leave,
                        // we can pre-allocate that the train is approaching this station.
                        station_approaching_train[id] = sender_signal_train_id;
                        prev_awaiting_empty_buffer = false;
                        prev_station_leaving_train_id = -1;
                        printf("Station %d BUFFER_EMPTY for Station %d for Train %d.\n", id, sender_signal_id, sender_signal_train_id);
                        signal_to_signal[sender_signal_id] ! BUFFER_EMPTY, id, sender_signal_train_id;
                    fi
                }
            :: sender_data == BUFFER_EMPTY ->
                if
                :: station_occupied_train[id] != -1 ->
                    atomic {
                        printf("Station %d allowing Train %d departure.\n", id, station_occupied_train[id]);
                        signal_to_train[station_occupied_train[id]] ! DEPART, id;
                        station_occupied_train[id] = -1;

                        // If there is a train in the buffer, tell it to move into the current station.
                        if
                        :: station_approaching_train[id] != -1 && trains_state[station_approaching_train[id]] == APPROACHING ->
                            printf("Station %d shifting Train %d out of buffer.\n", id, station_approaching_train[id]);
                            station_occupied_train[id] = station_approaching_train[id];
                            station_approaching_train[id] = -1;
                            signal_to_train[station_occupied_train[id]] ! STOP_IN_STATION, id;
                        :: else ->
                            skip
                        fi

                        // If there is a train awaiting to leave in the previous stations,
                        // signal it to leave:
                        if
                        :: prev_awaiting_empty_buffer ->
                            printf("Station %d detected previous station has a departing Train %d.\n", id, prev_station_leaving_train_id);
                            prev_awaiting_empty_buffer = false;
                            station_approaching_train[id] = prev_station_leaving_train_id;
                            prev_station_leaving_train_id = -1;
                            signal_previous_station ! BUFFER_EMPTY, id, prev_station_leaving_train_id;
                        :: else ->
                            skip;
                        fi
                    }
                :: else ->
                    printf("Station %d got buffer empty signal, but no trains were occupied in station!\n", id);
                fi
            :: sender_data == BUFFER_FULL ->
                printf("Station %d got buffer full signal from Station %d.\n", id, sender_signal_id)
                skip;
            :: else ->
                printf("INFO :: Unhandled sender data from station %d towards station %d of value %d.\n", sender_signal_id, id, sender_data);
            fi
        fi
    od
}

proctype train(int id){
    printf("Process %d for train %d.\n", _pid, id);
    do
    :: true ->
        // Assigned when recieving signal's command from channels.
        mtype:signal_command command;
        int sender_signal_id;

        mtype:train_state curr_train_state = trains_state[id];
        int curr_target_station = trains_station[id];

        if
        :: curr_train_state == STOPPED ->
            atomic {
                // Train is stopped, assumed all passenges deposited/recieved and signal ready to depart.
                trains_state[id] = READY_TO_DEPART;
                printf("Train %d relaying departure information to Signal %d.\n", id, curr_target_station);
                train_to_signal[curr_target_station] ! READY_TO_DEPART, id;
            }
        :: curr_train_state == READY_TO_DEPART ->
            // Train is already ready, recieve signal from station
            signal_to_train[id] ? command, sender_signal_id;

            atomic {
                if
                :: command == DEPART && sender_signal_id == curr_target_station ->
                    // Start departing to the next station
                    printf("Train %d got departure command from Signal %d.\n", id, sender_signal_id);
                    trains_state[id] = IN_TRANSIT;

                    int next_station_id = (sender_signal_id + 1) % STATION_COUNT;
                    printf("Train %d from current %d going to %d\n", id, trains_station[id], next_station_id);
                    trains_station[id] = next_station_id;
                :: else -> 
                    printf("Train %d got unknown command from Signal %d to perform %d when it is departing...\n", id, sender_signal_id, command);
                fi
            }
        :: curr_train_state == IN_TRANSIT ->
            atomic {
                // Train is already in transit, start signalling approaching instead.
                trains_state[id] = APPROACHING;
                printf("Train %d relaying approach information to Signal %d.\n", id, curr_target_station);
                train_to_signal[curr_target_station] ! APPROACHING, id;
            }
        :: curr_train_state == APPROACHING ->
            // In a station's buffer, recieve command to wait/enter.
            signal_to_train[id] ? command, sender_signal_id;
            if
            :: command == STOP_IN_STATION && sender_signal_id == curr_target_station ->
                printf("Train %d got command to unload/load at station (Signal %d).\n", id, curr_target_station);
                trains_state[id] = STOPPED;
            :: else ->
                printf("INFO :: Train %d got unknown command from Signal %d to perform %d when it is approaching...\n", id, sender_signal_id, command);
            fi
        :: else -> 
            printf("INFO :: Train %d got unhandled train status of %d.\n", id, curr_train_state);
        fi
    od
}
 
init {
    assert(TRAIN_COUNT > 0);
    assert(STATION_COUNT > 0);
    assert(STATION_COUNT >= TRAIN_COUNT);

    if
    :: (TRAIN_COUNT == 0 || STATION_COUNT == 0) -> skip;
    :: else -> 
        // Init all stations to have no trains in buffer.
        int i;
        for (i : 0 .. STATION_COUNT-1) {
            station_approaching_train[i] = -1;
        }

        // Init all trains to be stopped in a different station in ascending order.
        for (i : 0 .. TRAIN_COUNT-1) {
            trains_state[i] = STOPPED;
            trains_station[i] = i;
            station_occupied_train[i] = i;
        }


        atomic {
            for (i : 0 .. STATION_COUNT-1) {
                if
                :: i < TRAIN_COUNT -> run train(i);
                :: else -> skip;
                fi
                int next_station_id = (i + 1) % STATION_COUNT;
                int prev_station_id = (i - 1 + STATION_COUNT) % STATION_COUNT;
                printf("DEBUG :: Station %d, Next %d, Prev %d.\n", i, next_station_id, prev_station_id);
                run signal(i, signal_to_signal[next_station_id], signal_to_signal[prev_station_id]);
            }
        }
    fi;
}
