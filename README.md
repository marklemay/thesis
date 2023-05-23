# Mark Lemay's Thesis
[![Build LaTeX document](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml/badge.svg)](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml)
 
[Latest pdf](https://github.com/marklemay/thesis/releases/download/thesis/thesis.pdf)

## Defense

[slides](https://docs.google.com/presentation/d/1Wu5-xCrxIq7K_Z7SwQQCLUdGMcU2h0LRNY-4iHMU-uo/edit?usp=sharing)

Successfully defended May 24th. 
I am interested in doing an encore presentation that I could record, contact me if you are interested.
 
## compile pdf
Get bibliography and fully build BU style pdf with
```
git submodule foreach git pull origin master
latexmk thesis.tex -pdf
```
 
Build draft pdf, with margin notes and single spaced lines
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
