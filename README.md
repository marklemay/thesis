# Mark Lemay's Thesis: A Dependently Typed Programming Language With Dynamic Equality
[![Build LaTeX document](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml/badge.svg)](https://github.com/marklemay/thesis/actions/workflows/build-thesis.yml)
 
[Latest pdf](https://github.com/marklemay/thesis/releases/download/thesis/thesis.pdf) [proquest](https://www.proquest.com/docview/2835809556) [open.bu](https://open.bu.edu/handle/2144/46440)


## Defense

[slides](https://docs.google.com/presentation/d/1Wu5-xCrxIq7K_Z7SwQQCLUdGMcU2h0LRNY-4iHMU-uo/edit?usp=sharing)

Successfully defended May 24th.

A pesentation covering similar info was given at 
[TyDe2023](https://www.youtube.com/watch?v=nRnK365y9ac&list=PLyrlk8Xaylp4YYkJKQZ8gO9RK8GCqmFzk&index=5&ab_channel=ACMSIGPLAN).
 
## compile pdf
Get bibliography and fully build BU style pdf with
```
git submodule foreach git pull origin master
latexmk thesis.tex -pdf
```
 
Build thesis with my preferred formating
```
git submodule foreach git pull origin master
latexmk thesis-preferred-format.tex -pdf
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
