# Electrum

This tool provides an analyzer for Electrum models as an extension to the Alloy Analyzer.

### Building Electrum

Electrum needs Java 8 and can be built using Maven. The script will also build Kodkod/Pardinus, which uses the [Waf](https://github.com/waf-project/waf) build
system, which requires Python 2.5 or later, and needs a C/C++ compiler for the underlying solvers.

* Clone the Electrum repository, as well as Pardinus' as a submodule 

  `$ git clone -b master --recursive https://github.com/nmacedo/Electrum`  
  `$ cd Electrum`

* Run the Maven script to generate a self containable executable under `electrum/target`. This will compile Electrum and Pardinus, as well as the underlying native libraries (see respective installation [notes](https://github.com/nmacedo/Pardinus)).

 `$  mvn clean package -DskipTests`

### Running

[Download]() the executable ``jar`` (or [build](#building-electrum) it) and launch it simply as

`$ java -jar electrum-runnable.jar`

This will launch Electrum's/Alloy Analyzer's simple GUI, which is packaged with several examples.
