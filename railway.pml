#define TRAIN_COUNT 4
#define STATION_COUNT 4

// NOTE: Honestly, APPROACHING and IN_BUFFER doesn't have a logical effect,
// its just seperated for clarity and easier debug/trace.
// NOTE2: 'STOPPED' just means stopped in station, as compared to 'IN_BUFFER'.
mtype:train_state = {STOPPED, IN_TRANSIT, APPROACHING, IN_BUFFER, READY_TO_DEPART};
mtype:signal_command = {STOP_IN_BUFFER, STOP_IN_STATION, DEPART};
mtype:signal_information = {BUFFER_FULL, BUFFER_EMPTY, QUERY_BUFFER};

mtype:train_state trains_state[TRAIN_COUNT];
// ID of Station the train's state is targeted towards.
int trains_station[TRAIN_COUNT];

// On an indexed ID, if the station has a train waiting to enter, will contain the train's ID (-1 otherwise)
int station_awaited_train[STATION_COUNT];
// In an indexed ID, if the station has a train in it, will contain the train's ID (-1 otherwise)
int station_occupied_train[STATION_COUNT];

chan train_to_signal[STATION_COUNT] = [0] of {mtype:train_state, int};
chan signal_to_train[TRAIN_COUNT] = [1] of {mtype:signal_command};

chan signal_to_signal[STATION_COUNT] = [2] of {mtype:signal_information, int};

proctype signal(int id; chan signal_next_station; chan signal_previous_station) {
    do :: true ->
        // Assigned when recieving from channels...
        mtype:trains_state sender_train_state;
        int sender_train_id;
        // Recieve and handle all incoming train message
        do :: nempty(train_to_signal[id])
            train_to_signal[id] ? sender_train_state, sender_train_id;

            if
            :: sender_train_state == READY_TO_DEPART ->
                // Assert the train that is messaging that it is ready to depart, is the train that is in it's station.
                assert(sender_train_id == station_occupied_train[id]);
                 // Query next station's buffer to see if train can leave.
                signal_next_station ! QUERY_BUFFER, id;
            :: sender_train_state == IN_TRANSIT ->
                // A signal shouldn't have allowed another train to be in transit to another station,
                // if the other station already has something in buffer.
                assert(station_awaited_train[id] == -1);

                if
                :: station_occupied_train[id] == -1 ->
                    // Nothing in station, reserve a slot in station
                    station_occupied_train[id] = sender_train_id;
                :: else -> 
                    // Station occupied, reserve a slot in buffer zone.
                    station_awaited_train[id] = sender_train_id;
                fi
            :: sender_train_state == APPROACHING ->
                if
                :: station_occupied_train[id] == -1 ||  station_occupied_train[id] == sender_train_id ->
                    // Nothing in station or already reserved for it, send to station.
                    station_occupied_train[id] = sender_train_id;
                    signal_to_train[sender_train_id] ! STOP_IN_STATION;
                :: else ->
                    // Station occupied, send to buffer zone.
                    station_awaited_train[id] = sender_train_id;
                    signal_to_train[sender_train_id] ! STOP_IN_BUFFER;
                fi
            fi
        od

        mtype:signal_information sender_data;
        int sender_station_id;
        // Recieve and handle all incoming signal message
        do :: nempty(signal_to_signal[id])
            signal_to_signal[id] ? sender_data, sender_station_id;

            if
            :: sender_data == QUERY_BUFFER ->
                // Send buffer status depending if there is a train in buffer zone...
                if
                :: station_awaited_train[id] == -1 -> signal_to_signal[sender_station_id] ! BUFFER_EMPTY, id;
                :: else -> signal_to_signal[sender_station_id] ! BUFFER_FULL, id;
                fi
            :: sender_data == BUFFER_FULL ->
                if
                :: station_occupied_train[id] != -1 ->
                    // Tell any ready train to wait.
                    signal_to_train[station_occupied_train[id]] ! STOP_IN_STATION;
                :: else -> skip; 
                fi
            :: sender_data == BUFFER_EMPTY ->
                if
                :: station_occupied_train[id] != -1 ->
                    // Tell the ready train to move.
                    signal_to_train[station_occupied_train[id]] ! DEPART;
                    // If there is a train in the buffer, tell it to move into the current station.
                    if
                    :: station_awaited_train[id] != -1 ->
                        signal_to_train[station_awaited_train[id]] ! STOP_IN_STATION;
                        station_occupied_train[id] = station_awaited_train[id];
                        station_awaited_train[id] = -1;
                    :: else ->
                        station_occupied_train[id] = -1;
                    fi
                :: else -> skip
                fi
                // Inform the previous station that it is currently ready to accept trains.
                signal_previous_station ! BUFFER_EMPTY, id;
            fi
        od
    od
}

proctype train(int id){
    do :: true ->
        // Assigned when recieving signal's command from channels.
        mtype:signal_command command;

        mtype:train_state curr_train_state = trains_state[id];
        int curr_target_station = trains_station[id];

        if
        :: curr_train_state == STOPPED ->
            // Train is stopped, assumed all passenges deposited/recieved and signal ready to depart.
            trains_state[id] = READY_TO_DEPART;
            train_to_signal[curr_target_station] ! READY_TO_DEPART, id;
        :: curr_train_state == READY_TO_DEPART ->
            // Train is already ready, recieve signal from station
            signal_to_train[id] ? command;
            if
            :: command == DEPART ->
                // Start departing to the next station
                trains_state[id] = IN_TRANSIT;

                int next_station_id = (curr_target_station + 1) % STATION_COUNT;
                trains_station[id] = next_station_id;
                // Signal to the next station that it is in transit
                train_to_signal[next_station_id] ! IN_TRANSIT
            :: else -> 
                // No signal to depart yet, do nothing.
                skip
            fi
        :: curr_train_state == IN_TRANSIT ->
            // Train is already in transit, start signalling approaching instead.
            trains_state[id] = APPROACHING;
            train_to_signal[curr_target_station] ! APPROACHING, id;
        :: curr_train_state == APPROACHING || curr_train_state == IN_BUFFER ->
            // In a station's buffer, recieve command to wait/enter.
            signal_to_train[id] ? command;
            if
            :: command == STOP_IN_BUFFER ->
                // Wait in buffer area
                trains_state[id] = IN_BUFFER;
            :: command == STOP_IN_STATION ->
                // Stop in station.
                trains_state[id] = STOPPED;
            fi
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
        // Init all stations to have no trains in station/buffer.
        int i;
        for (i : 0 .. STATION_COUNT-1) {
            station_occupied_train[i] = -1;
            station_awaited_train[i] = -1;
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
                run signal(i, signal_to_signal[next_station_id], signal_to_signal[prev_station_id]);
            }
        }
    fi;
}
