# Examples

To compile the example to TLA+ execute

```
java -cp ../dist/tla2tools.jar pcal.trans [-label] <path to algo>/<algo>
```

## Simple examples with threads

- [ ]
  [ThreadsC.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsC.tla):
  simple example with single- and multi-threaded processes 

To compile the example to TLA+ execute
```
java -cp ../dist/tla2tools.jar pcal.trans ThreadsC.tla
```

- [ ]
  [ThreadsP.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsP.tla):
  same as ThreadsC.tla but with P-syntax

- [ ]
  [ThreadsMacro.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsMacro.tla):
  simple example with threads using a macro 

- [ ]
  [ThreadsProcedure.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsProcedure.tla):
  simple example with threads using a procedure 

- [ ]
  [ThreadsFairness.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsFairness.tla):
  simple example with threads using various fairness conditions


## Channels

- [ ]
  [ChannelsC.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ChannelsC.tla):
- [ ]
  [ChannelsMulticast.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ChannelsMulticast.tla):
- [ ]
  [ChannelsBroadcast.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ChannelsBroadcast.tla):

## Mutual exclusion algorithm
- [ ]
  [LamportMutex.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/LamportMutex.tla):
	Lamport's distributed mutual-exclusion algorithm. To model-check use [MCLamportMutex.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/MCLamportMutex.tla)

## Paxos consensus algorithm
- [ ]
  [Paxos.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/Paxos.tla): The Paxos consensus algorithm.
