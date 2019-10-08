Electrum is an extension to the Alloy Analyzer by [INESC TEC](https://www.inesctec.pt/en) (the Institute for Systems and Computer Engineering, Technology and Science) and [ONERA](https://www.onera.fr/en) (the French aerospace research center) provides an analyzer for Electrum models, a temporal extension to the Alloy modeling language. The Analyzer provides both bounded and unbounded model checking procedures.

[Alloy](http://alloy.mit.edu/) is a simple structural modeling language based on first-order logic developed at the [Software Design Group](http://sdg.csail.mit.edu/). Its Analyzer can generate instances of invariants, simulate the execution of operations, and check user-specified properties of a model.

## Getting started

The best way to get started with Electrum is to download the executable ``jar`` (see [Running](#running)) and follow the [tutorial](https://github.com/haslab/Electrum/wiki/Tutorial). You can also watch the following video for an overview. (The video was recorded for Electrum 1, so there may be slight changes on the interface.)

<div align="center">
<a href="http://www.youtube.com/watch?feature=player_embedded&v=FbjlpvjgMDA
" target="_blank"><img src="http://img.youtube.com/vi/FbjlpvjgMDA/0.jpg" 
alt="Electrum Video" width="480"  border="10" /></a></div>

A repository of examples, including familiar Alloy examples converted into Electrum, is also available [here](https://github.com/haslab/Electrum2/wiki).

## Running

[Download](https://github.com/haslab/Electrum2/releases/tag/v2.0) the executable ``jar`` and launch it simply as

`$ java -jar electrum2.0.jar`

This will launch Electrum's/Alloy Analyzer's simple GUI, which is packaged with several examples. The file can also by run from the command-line, for more information run

`$ java -jar electrum2.0.jar --help`

To perform analyses on an unbounded time horizon, one needs to have installed [Electrod](https://github.com/grayswandyr/electrod/) program, as well as [NuSMV](http://nusmv.fbk.eu/) or [nuXmv](https://nuxmv.fbk.eu/).

## Building Electrum Analyzer

The Electrum Analyzer 2 inherits the building [instructions](https://github.com/haslab/Electrum2#tldr) from Alloy Analyzer 5.

## Prototype: Electrum with actions

An [extension of Electrum 1](https://github.com/haslab/Electrum/releases/tag/v1.0-actions), with actions, is currently under study. Check out the [paper](https://doi.org/10.1007/978-3-319-91271-4_30) with the preliminary proposition.

If you wish to build it, follow the [building](https://github.com/haslab/Electrum#building-electrum-analyzer) steps for Electrum 1, just replacing `-b master` in the first line by `-b actions`.

## ERTMS Case Study
Our response to the ABZ 2018 call for case study submissions, the ERTMS system, can be found [here](https://github.com/haslab/Electrum/wiki/ERTMS). Or access directly the:
* Electrum [model](http://haslab.github.io/Electrum/ertms.ele) and [theme](http://haslab.github.io/Electrum/ertms.thm)
* Alloy [model](http://haslab.github.io/Electrum/ertms.als) and [theme](http://haslab.github.io/Electrum/ertms_als.thm)
* Accepted [paper](http://haslab.github.io/Electrum/ertms.pdf) describing its development

## License

Electrum is open-source and available under the [MIT license](https://github.com/haslab/Electrum/blob/master/electrum/LICENSE), as is the Alloy Analyzer. However, it utilizes several third-party packages whose code may be distributed under a different license (see the various [LICENSE files](https://github.com/haslab/Electrum/tree/master/LICENSES) in the distribution for details), including [Kodod](https://github.com/emina/kodkod) and its extension [Pardinus](https://github.com/haslab/Pardinus), and the underlying solvers ([SAT4J](http://www.sat4j.org), [MiniSat](http://minisat.se), [Glucose/Syrup](http://www.labri.fr/perso/lsimon/glucose/), [(P)Lingeling](http://fmv.jku.at/lingeling/), [Yices](http://yices.csl.sri.com), [zChaff](https://www.princeton.edu/~chaff/zchaff.html), [CryptoMiniSat](https://www.msoos.org/cryptominisat5/) and [Electrod](https://github.com/grayswandyr/electrod/). [CUP](http://www2.cs.tum.edu/projects/cup/) and [JFlex](http://jflex.de/) are also used to generate the parser. 

## Collaborators
- Nuno Macedo, HASLab, INESC TEC & Universidade do Minho, Portugal
- Julien Brunel, ONERA/DTIS & Université fédérale de Toulouse, France
- David Chemouil, ONERA/DTIS & Université fédérale de Toulouse, France
- Alcino Cunha, HASLab, INESC TEC & Universidade do Minho, Portugal
- Denis Kuperberg, TU Munich, Germany
- Eduardo Pessoa, HASLab, INESC TEC & Universidade do Minho, Portugal

## History
### Electrum [2.0](https://github.com/haslab/Electrum2/releases/tag/v2.0) (October 2019) 
<!--- FM Tutorial -->
- Rebased to Alloy Analyzer 5
- Slight changes to the language
- Trace visualizer with additional exploration operations

### Electrum [1.2](https://github.com/haslab/Electrum/releases/tag/v1.2) (April 2019) 
- Several improvements and bug fixes to the interface, visualiser and evaluator

### Electrum [1.1](https://github.com/haslab/Electrum/releases/tag/v1.1) (May 2018) 
<!--- ASE18 submission, ABZ18 attendance -->
- Initial support for symbolic bound extraction
- Repository of examples
- Many enhancements and bug fixes
- Accompanied the ASE'18 [submission](https://doi.org/10.1145/3238147.3240475)

### Electrum [1.0](https://github.com/haslab/Electrum/releases/tag/v1.0) (January 2018) 
<!--- FM18,ABZ18 submissions, AlloyWorkshop attendance -->
- First stable public release (accompanying the ABZ'18 [submission](https://doi.org/10.1007/978-3-319-91271-4_21))
- Common interface for temporal relational model finding problems through Pardinus
- Bounded and unbounded model checking of Electrum models
- Uniform visualization of trace instances
- Support for a decomposed solving strategy

### Electrum [0.2](https://github.com/haslab/Electrum/releases/tag/v0.2) (November 2016) 
<!--- FSE16 attendance -->
- Direct embedding into a temporal extension to Kodkod ([Pardinus](https://github.com/haslab/Pardinus))
- Visualizer natively supports temporal solutions

### Electrum [0.1](https://github.com/haslab/Electrum/releases/tag/v0.1) (March 2016) 
<!--- FSE16 submission -->
- First release (accompanying the FSE'16 [submission](http://dx.doi.org/10.1145/2950290.2950318))
- Bounded model checking of Electrum models
- Electrum models expanded into Alloy models
- Expanded Alloy models returned to the visualizer

## Publications

Electrum has been developed in the context of the [TRUST](http://trust.di.uminho.pt/) project, and incorporates contributions from several publications:
- J. Brunel, D. Chemouil, A. Cunha and N. Macedo. **The Electrum Analyzer: Model checking relational first-order temporal specifications.** In the proceedings ASE'18. ACM, 2018.
- A. Cunha and N. Macedo. **Validating the Hybrid ERTMS/ETCS Level 3 concept with Electrum.** In the proceedings of ABZ'18. LNCS 10817. Springer, 2018. 
- J. Brunel, D. Chemouil, A. Cunha, T. Hujsa, N. Macedo and J. Tawa. **Proposition of an action layer for Electrum.** In the proceedings of ABZ'18. LNCS 10817. Springer, 2018. 
- N. Macedo, A. Cunha and E. Pessoa. **Exploiting partial knowledge for efficient model analysis.** In the proceedings of ATVA'17. LNCS 10482. Springer, 2017.
- N. Macedo, J. Brunel, D. Chemouil, A. Cunha and D. Kuperberg. **Lightweight specification and analysis of dynamic systems with rich configurations.** In the proceedings of FSE'16. ACM, 2016.
- N. Macedo, A. Cunha and T. Guimarães. **Exploring scenario exploration.** In the proceedings of FASE'15. LNCS 9033. Springer, 2015.
- A. Cunha, N. Macedo and T. Guimarães. **Target oriented relational model finding.** In the proceedings of FASE'14. LNCS 8411. Springer, 2014.
