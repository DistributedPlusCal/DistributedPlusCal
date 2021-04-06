# Distributed PlusCal

- initialize git repository from this repository's URL (check import projects when done checkbox)
- import maven project from repository (no need if the previous checkbox was checked)
- make sure the installed jre is 11, window -> preferences -> installed jres -> add (and give the url for the installed and set up jdk 11)
- clean and build project
- ant -f customBuild.xml compile
- ant -f customBuild.xml dist


-Translate from Distributed Pcal
  - navigate to trans.java inside pcal package
  - configure run command ex : "-distpcal /../../test.tla"

-Run translator
- java -cp dist/tla2tools.jar distpcal.trans -label <path to spec>/<spec>
- example: java -cp dist/tla2tools.jar pcal.trans -label examples/2PhaseCommit.tla
