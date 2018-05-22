# Electrum Analyzer

This extension to the Alloy Analyzer by [INESC TEC](https://www.inesctec.pt/en) (the Institute for Systems and Computer Engineering, Technology and Science) and [ONERA](https://www.onera.fr/en) (the French aerospace research center) provides an analyzer for Electrum models, a temporal extension to the Alloy modeling language. The Analyzer provides both bounded and unbounded model checking procedures.

[Alloy](http://alloy.mit.edu/) is a simple structural modeling language based on first-order logic developed at the [Software Design Group](http://sdg.csail.mit.edu/). Its Analyzer can generate instances of invariants, simulate the execution of operations, and check user-specified properties of a model.

## Running

[Download](https://github.com/haslab/Electrum/releases/tag/v1.1) the executable ``jar`` (or [build](#building-electrum-analyzer) it) and launch it simply as

`$ java -jar electrum-1.1.jar`

This will launch Electrum's/Alloy Analyzer's simple GUI, which is packaged with several examples. The file can also by run from the command-line, just check

`$ java -jar electrum-1.1.jar --help`

To perform analyses on an unbounded time horizon, one needs to install the [Electrod](https://github.com/grayswandyr/electrod/) program as well as [NuSMV](http://nusmv.fbk.eu/) or [nuXmv](https://nuxmv.fbk.eu/).

## Building Electrum Analyzer

The Electrum Analyzer requires Java 7 and can be built using Maven. The script will also build Kodkod/Pardinus.

* Clone the Electrum repository, as well as Pardinus' as a submodule 

  `$ git clone -b master --recursive https://github.com/haslab/Electrum`  
  `$ cd Electrum`

* Run the Maven script to generate a self containable executable under `electrum/target`. This will compile Electrum and Pardinus, and pack the available native libraries.

 `$  mvn clean package -DskipTests`

## Prototype: Electrum with actions

An [extension of Electrum](https://github.com/haslab/Electrum/releases/tag/v1.0-actions), with actions, is currently under study. 

If you wish to build it, repeat the steps above, just replacing `-b master` in the first line by `-b actions`.

## Collaborators
- Nuno Macedo, HASLab, INESC TEC & Universidade do Minho, Portugal
- Julien Brunel, ONERA/DTIS & Université fédérale de Toulouse, France
- David Chemouil, ONERA/DTIS & Université fédérale de Toulouse, France
- Alcino Cunha, HASLab, INESC TEC & Universidade do Minho, Portugal
- Denis Kuperberg, TU Munich, Germany
- Eduardo Pessoa, HASLab, INESC TEC & Universidade do Minho, Portugal

## ERTMS Case Study
Our response to the ABZ 2018 call for case study submissions, the ERTMS system, can be found [here](https://github.com/haslab/Electrum/wiki/ERTMS). Or access directly the:
* Electrum [model](http://haslab.github.io/Electrum/ertms.ele) and [theme](http://haslab.github.io/Electrum/ertms.thm)
* Alloy [model](http://haslab.github.io/Electrum/ertms.als) and [theme](http://haslab.github.io/Electrum/ertms_als.thm)
* Accepted [paper](http://haslab.github.io/Electrum/ertms.pdf) describing its development

## License

Electrum is open-source and available under the [MIT license](electrum/LICENSE), as is the Alloy Analyzer. However, it utilizes several third-party packages whose code may be distributed under a different license (see the various [LICENSE files](electrum/LICENSES) in the distribution for details), including [Kodod](https://github.com/emina/kodkod) and its extension [Pardinus](https://github.com/haslab/Pardinus), and the underlying solvers ([SAT4J](http://www.sat4j.org), [MiniSat](http://minisat.se), [Glucose/Syrup](http://www.labri.fr/perso/lsimon/glucose/), [(P)Lingeling](http://fmv.jku.at/lingeling/), [Yices](http://yices.csl.sri.com), [zChaff](https://www.princeton.edu/~chaff/zchaff.html), [CryptoMiniSat](https://www.msoos.org/cryptominisat5/) and [Electrod](https://github.com/grayswandyr/electrod/). [CUP](http://www2.cs.tum.edu/projects/cup/) and [JFlex](http://jflex.de/) are also used to generate the parser. 

## History
### Electrum [1.1](https://github.com/haslab/Electrum/releases/tag/v1.1) (May 2018) 
<!--- ASE 18 submission, ABZ 18 attendance -->
- Initial support for symbolic bound extraction
- Repository of examples
- Many enhancements and bug fixes

### Electrum [1.0](https://github.com/haslab/Electrum/releases/tag/v1.0) (January 2018) 
<!--- FM,ABZ 18 submissions, Alloy Workshop attendance -->
- First stable public release
- Common interface for temporal relational model finding problems through Pardinus
- Bounded and unbounded model checking of Electrum models
- Uniform visualisation of trace instances
- Support for a decomposed solving strategy
- Accompanied the ABZ'18 [submission](https://doi.org/10.1007/978-3-319-91271-4_21)


### Electrum [0.2](https://github.com/haslab/Electrum/releases/tag/v0.2) (November 2016) 
<!--- FSE 16 attendance -->
- Direct embedding into a temporal extension to Kodkod ([Pardinus](https://github.com/haslab/Pardinus))
- Visualizer natively supports temporal solutions

### Electrum [0.1](https://github.com/haslab/Electrum/releases/tag/v0.1) (March 2016) 
<!--- FSE 16 submission -->
- First release accompanying the FSE'16 [submission](http://dx.doi.org/10.1145/2950290.2950318)
- Bounded model checking of Electrum models
- Electrum models expanded into Alloy models
- Expanded Alloy models returned to the visualizer
