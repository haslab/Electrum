# Electrum


### Building Electrum

Electrum needs Java 8 and can be built using Maven. The script will also build Kodkod/Pardinus, which uses the [Waf](https://github.com/waf-project/waf) build
system, which requires Python 2.5 or later, and needs a C/C++ compiler for the underlying solvers.

* Clone the Electrum repository, as well as Pardinus' as a submodule 

 `$ git clone -b master --recursive https://github.com/nmacedo/Electrum`
 `$ cd Electrum`

* Run the Maven script to generate a self containable executable. This will compile Electrum/Pardinus, as well as the underlying native libraries (see []())

 `$ mvn clean install`

### Running

[Download]() the executable ``jar`` (or [build]() it) and launch it simply as

`$ java electrum.jar`

This will launch Electrum's/Alloy Analyzer's simple GUI.
