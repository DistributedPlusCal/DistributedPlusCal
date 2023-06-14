# Examples

To build the pcal/distpcal compiler use

```
ant -f customBuild.xml compile
ant -f customBuild.xml dist
```

To compile an algorithm

```
java -cp <path to TLA distrib>/dist/tla2tools.jar pcal.trans [-label] <path to algo>/<algo>
```

