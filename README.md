# thesis
all work related to my thesis document, will eventually become public
[![Build LaTeX document](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml/badge.svg)](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml)

latest draft availible [here](https://github.com/marklemay/thesis/releases)

## What to Review
* Where are you first confused?
* Where do you first get board?
* how much new jargon sould I introduce
  * name the system `dDyamic`?
  * better name for the `surface langugae` and `cast langugae`?
  * `gradual correctness`?

* Chapter 1
  * is a pluasable argument made
  * spelling grammar
* Chapter 2
  * proofs correct 
  * formalisms are well motivated
  * formalisms are "standard"
  * prior work is correct
  * spelling grammar
* Chapter 3
  * proofs correct 
  * formalisms are well motivated
* Chapter 4
  * formalisms are well motivated
  * prior work is correct, and complete
* Chapter 5
  * examples
* Conclusion
  * photo ready

## compile pdf
get bibliography and fully build bu style pdf with
```
git submodule foreach git pull origin master
latexmk thesis.tex -pdf
```

build draft pdf, with notes and double sided margins
```
git submodule foreach git pull origin master
latexmk draft.tex -pdf
```

## Complete
* 6/16/2021 thesis proposal
- [x] June
  - [x] Propose
  - [x] extended abstract submission
- [x] July
  - [x] reworked data
- [x] August
  - [x] Begin a submission to [CPP](https://popl22.sigplan.org/home/CPP-2022)
- [x] September
  - [x] Submit to [CPP](https://popl22.sigplan.org/home/CPP-2022)
  - [x] Produce some larger examples
- [x] October
  - [x] draft Surface Language chapter
- [x] November
  - [x] draft Cast Language chapter
  - [x] draft Surface Data chapter
## Plan
- [ ] December
  - [x] draft Cast Data chapter
  - [x] draft introduction
  - [x] draft conclusion
- [ ] Jan
  - [ ] finalize thesis
  - [ ] Send to commitee (at least 2 weeks before defense)
- [ ] Feb
  - [ ] Practice defence
  - [ ] Defend
## Remove from the body of the thesis
- [ ] Rework symbolic execution to work in the cast language
- [ ] draft testing chapter
- [ ] draft runtime proof search chapter



## TODO
* formatting
* join one of the writing groups/workshops?
* CI

## Related
* https://github.com/marklemay/boston-university-thesis-template
* https://github.com/marklemay/thesis-proposal
* https://icfp21.sigplan.org/details/TyDe-2021/1/Gradual-Correctness-a-Dynamically-Bidirectional-Full-Spectrum-Dependent-Type-Theory-
  * https://github.com/marklemay/dDynamic
  * https://github.com/qcfu-bu/dtest-coq

