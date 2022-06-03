# Mark Lemay's Thesis
[![Build LaTeX document](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml/badge.svg)](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml)
 
[Latest draft](https://github.com/marklemay/thesis/releases/download/thesis/thesis.pdf)

## Defense

[slides](https://docs.google.com/presentation/d/1Wu5-xCrxIq7K_Z7SwQQCLUdGMcU2h0LRNY-4iHMU-uo/edit?usp=sharing)

Successfully defended May 24th. 
I am interested in doing an encore presentation that I could record, contact me if you are interested.

## How to Review
Printed draft chapters are in the draft folder by my desk.
Ask me if you would like a pdf with custom formatting (for instance single spaced, editing notes included), or your own printed copy.
### Overall
* Where are you first confused?
* Where do you first get bored?
* What is 1 thing you would like an example of?
* how much new jargon should I introduce
  * name the programming language? `dDyamic`? `dTest`?
  * better name for the `surface language` and `cast language`?
  * `gradual correctness`?
* prior work is complete and well represented
* proofs are correct
* formalisms are well motivated
### Specifically
* Chapter 1
  * should be readable by a general audience
* Chapter 2
  * formalisms are "standard"
 
## compile pdf
get bibliography and fully build BU style pdf with
```
git submodule foreach git pull origin master
latexmk thesis.tex -pdf
```
 
build draft pdf, with margin notes and single spaced lines
```
git submodule foreach git pull origin master
latexmk draft.tex -pdf
```

## Related
* https://github.com/marklemay/boston-university-thesis-template
* https://github.com/marklemay/thesis-proposal
* https://icfp21.sigplan.org/details/TyDe-2021/1/Gradual-Correctness-a-Dynamically-Bidirectional-Full-Spectrum-Dependent-Type-Theory-
  * https://github.com/marklemay/dDynamic
  * https://github.com/marklemay/dtest-coq2
  * https://github.com/qcfu-bu/dtest-coq


## Admin
* https://docs.google.com/spreadsheets/d/19Mxe4p4qDgGDf7lBmWTGsI0m9lmP4FuxVyHD_kRM7-g/edit#gid=0
