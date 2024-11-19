#define N 4 //max number of trains
#define M 4 //max number of stations


mtype = {IN_TRANSIT, APPROACHING, STOPPED};

//you must decide the size of the arrays, the type of channels (synchronous/asynchronous), and their buffer size for assynchronous channels.

mtype trains_state[] = {STOPPED, STOPPED, STOPPED, STOPPED};

int trains_station[] = {}; //you can assign values statically or dinamically at the beginning of the model (in the init process or in the train process)

chan train_to_signal[] = [] of {mtype, int};
chan signal_to_signal[] = [] of {mtype, int};
  
proctype train(int id){
    //define the necessary local variables, if any.
    //the train process must be a reactive system that is always travelling from station to station.
    // you can decide at the beginnig the station where the train is stopped and the state of the train.
    //after variables have been initialized the train will be in a loop where it will be always moving from station to station.

    do :: true -> //define the behavior of the train in the different states
    od
    }

    proctype signal(int id, chan signal_next_station, chan signal_previous station){
    //define the necessary local variables, if any.
    //after variables have been initialized signals will be in a loop waiting for signals from trains or other stations.

    do :: true -> //define the behavior of the signal in the different states
    od

}
 
init{ 
    // create the processes with the necessary arguments and right values the following lines are just examples.

    run train(0);
    run signal(0, signal_to_signal[0], signal_to_signal[N-1]);
}