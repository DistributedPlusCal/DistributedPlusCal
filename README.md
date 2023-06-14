# Distributed PlusCal

## Get the distrib

```
git clone git@github.com:DistributedPlusCal/DistributedPlusCal.git
```

## Build the distrib

(you can skip to next step if you don't want the latest version)

```
cd DistributedPlusCal/tlatools
mkdir test-class
ant -f customBuild.xml clean
ant -f customBuild.xml compile
ant -f customBuild.xml dist
```

## Run it on examples

```
java -cp <path to TLA distrib>/tlatools/dist/tla2tools.jar pcal.trans [-label] <path to algo>/<algo>
```

For example, if current directory is `DistributedPlusCal/tlatools`,

```
java -cp dist/tla2tools.jar pcal.trans examples-distpcal/ThreadsC.tla
```
