# Mark Lemay's Thesis
[![Build LaTeX document](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml/badge.svg)](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml)
 
[Latest draft](https://github.com/marklemay/thesis/releases/download/thesis/thesis.pdf)

## Defence
(this is open to the public, but if you plan to attend in person it would be good to reach out so I can book a bigger room if needed)
 
(contact me if you want a zoom link)
 
The defense is scheduled for:
 
* May 24th at 11:00 am(EST) in BU's MCS B21
 
Practice Defenses:
 
* May 17th at 7:00 pm (EST) online only

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
- [x] December
  - [x] draft introduction
  - [x] draft conclusion
- [x] Jan
  - [x] discovered mistake in handling of data
- [x] Feb
  - [x] redo data
  - [x] revise introduction
  - [x] revise Surface Language chapter, Cast Language chapter
  - [x] send draft to committee
- [x] March
  - [x] ICFP submission
  - [x] reimplement
## Plan
- [x] April
  - [x] bug fixing/ testing
  - [x] rewrite Data chapter
  - [ ] revise final 3 chapters
  - [ ] re-apply for an extention
  - [ ] schedual defense
  - [ ] Practice defense
  - [ ] Defend

## Related
* https://github.com/marklemay/boston-university-thesis-template
* https://github.com/marklemay/thesis-proposal
* https://icfp21.sigplan.org/details/TyDe-2021/1/Gradual-Correctness-a-Dynamically-Bidirectional-Full-Spectrum-Dependent-Type-Theory-
  * https://github.com/marklemay/dDynamic
  * https://github.com/marklemay/dtest-coq2
  * https://github.com/qcfu-bu/dtest-coq


## Admin
* https://docs.google.com/spreadsheets/d/19Mxe4p4qDgGDf7lBmWTGsI0m9lmP4FuxVyHD_kRM7-g/edit#gid=0
