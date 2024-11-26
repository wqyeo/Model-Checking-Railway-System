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
// Signal information, signal id, train id
chan signal_to_signal[STATION_COUNT] = [4] of {mtype:signal_information, int, int};

//#region LTL

// https://spinroot.com/spin/Man/ltl.html
// NOTE: Wording of 'First' refers to index 0.
// NOTE2: LTL check only works with 4 trains and 4 stations...

// NOTE: p1
// If train0 is waiting to enter in the station1, it will eventually enter the station.
ltl first_train_eventually_enter_next_station { 
    eventually (
        (trains_state[0] == APPROACHING && trains_station[0] == 1) 
        until
        (trains_state[0] == STOPPED)
    ) 
}

// NOTE: p2
// Always happens that some time in the future train1 will enter station3.
ltl second_train_always_eventually_enter_fourth_station { 
    always eventually (trains_station[1] == 3)
}


// NOTE: p3
// Always eventually happens that train1 will be eventually in a station with an index small tahn the station in which train 4 is stopped;
// (Assumption: Train4 needs to be stopped, but train1 doesn't need to be)
ltl second_train_always_eventually_in_station_before_fourth_train { 
    always eventually (
        trains_station[1] < trains_station[3] &&
        (trains_state[3] == STOPPED || trains_state[3] == READY_TO_DEPART)
    ) 
}

// NOTE: p4
// Always eventually happens that all trains will be stopped in some station.
// NOTE: Ready to depart is same as being stopped in the station. (Just held up from leaving)
ltl all_trains_always_eventually_stop { 
    always eventually (
        (trains_state[0] == STOPPED || trains_state[0] == READY_TO_DEPART) &&
        (trains_state[1] == STOPPED || trains_state[1] == READY_TO_DEPART) &&
        (trains_state[2] == STOPPED || trains_state[2] == READY_TO_DEPART) &&
        (trains_state[3] == STOPPED || trains_state[3] == READY_TO_DEPART)
    )
}

// NOTE: p5
// Never can happen that two trains are in the same station in either transit or approaching states.
active proctype assert_never_two_trains_in_same_station_approaching_transit() {
    int i, j;
    end_assert:
    do
    ::
        i = 0;
        do
        :: i < TRAIN_COUNT ->
            j = 0;
            do
            :: j < TRAIN_COUNT ->
                if
                :: j == i ->
                    // Skip same train comparison
                    skip;
                :: else ->
                    // NOT: 2 trains in targetting station, and they are both approaching/transit.
                    assert(!(
                        trains_station[i] == trains_station[j] 
                        && (trains_state[i] == APPROACHING || trains_state[i] == IN_TRANSIT) && 
                        (trains_state[j] == APPROACHING || trains_state[j] == IN_TRANSIT)
                    ))
                fi;
                j++;
            :: else ->
                break;
            od;
            i++;
        :: else ->
            break;
        od;
    od;
}

//#endregion

/**
Infinite loop that on each cycle, does
    - Handle train messages (channel)
    - Handle signal messages (channel)
Note that cycle is blocking if both channel is empty (no messages), until a message appears.

## Handling Train message:
Only handles train state for 'Ready to depart' and 'Approaching'.

If a train is ready to depart, it will just query the next signal for it's buffer status (empty/full).

If a train is approaching, it will check if itself has space for the train to dock in station.
If so, it will let the train dock into the station, otherwise it will just hold up the train.

## Handling Signal Messages
Only handles incoming signal for Empty Buffer or Query Buffer.

If a signal (usaually previous) is querying it's buffer status,
it will reply back with a status of EMPTY/FULL.
    - EMPTY: No train approaching/transit on self.
    - FULL: A train approaching/transit on self.
Additionally, if its FULL, it will store in memory that the previous signal
was awaiting for an empty slot in it's buffer.

If a signal replied back to self with Empty Buffer, it will:
    1. Send the currently ready to depart train to next station.
    2. Bring any currently approaching train to dock into self station.
    3. If previous signal was awaiting for an empty slot in it's buffer,
    it will send to the previous signal that it is now EMPTY.
 */
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

/**
State machine update logic.

On each cycle,

## Train state is STOPPED (docked in station)
Immediately switch to being ready to depart,
inform current station that it wants to depart..

## Train state is Ready to depart
Await any signal from current station. If its a depart signal, depart immediately.
(Proceed to transit state)

## Train state is Transit
Immediately switch to approaching state,
inform current station that it is approaching.

## Train state is Approaching
Await any signal from current station.
If its a stop (dock) signal, dock into current station
(Switch to STOPPED state)
 */
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
            // Train is already in transit, start signalling approaching instead.
            trains_state[id] = APPROACHING;
            printf("Train %d relaying approach information to Signal %d.\n", id, curr_target_station);
            train_to_signal[curr_target_station] ! APPROACHING, id;
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
    assert(STATION_COUNT > 1);
    assert(STATION_COUNT >= TRAIN_COUNT);

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
}
