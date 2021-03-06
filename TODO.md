library request
* ~~https://link.springer.com/book/10.1007/978-1-4471-0963-1~~
* print https://link-springer-com.ezproxy.bu.edu/content/pdf/10.1007%2FBFb0037116.pdf
* https://arxiv.org/abs/2205.01241

Review/add citations
* "Saïbi [20] describes an elaboration mechanism inserting coercions between types."
  * Amokrane Saïbi. Typing algorithm in type theory with inheritance. Proceedings of the 24th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages - POPL ’97, 1997. doi:10.1145/263699.263742.
* https://arxiv.org/pdf/2011.10618.pdf
  * "Hybrid typing... In a similar manner, [Tanter and Tabareau 2015]
introduce casts for subset types with decidable properties in Coq. They use an axiom to denote
failure, which breaks weak canonicity. Dependent interoperability [Dagand et al. 2018; Osera et al.
2012] supports the combination of dependent and non-dependent typing through deep conversions.
All these approaches are more intended as programming languages than as type theories, and none
support the notion of (im)precision that is at the heart of gradual typing.
Dependent contracts. [Greenberg et al. 2010] relates hybrid typing to dependent contracts, which
are dynamically-checked assertions that can relate the result of a function application to its
argument [Findler and Felleisen 2002]. The semantics of dependent contracts are subtle because
contracts include arbitrary code, and in particular one must be careful not to violate the precondition
on the argument in the definition of the postcondition contract [Blume and McAllester 2006]. Also,
blame assignment when the result and/or argument are themselves higher-order is subtle. Different
variants of dependent contracts have been studied in the literature, which differ in terms of the
violations they report and the way they assign blame [Dimoulas et al. 2011; Greenberg et al. 2010].
An in-depth exploration of blame assignment for gradual dependent type theories such as GCIC is
an important perspective for future work.
Gradual typing. The blame calculus of Wadler and Findler [2009] considers subset types on
base types, where the refinement is an arbitrary term, as in hybrid type checking [Knowles and
Flanagan 2010]. It however lacks the dependent function types found in other works. Lehmann
and Tanter [2017] exploit the Abstracting Gradual Typing (AGT) methodology [Garcia et al. 2016]
to design a language with imprecise formulas and implication. They support dependent function
types, but gradual refinements are only on base types refined with decidable logical predicates."
"[Eremondi et al. 2019]... study the dynamic
gradual guarantee, but not its reformulation as graduality [New and Ahmed 2018], which as we
explain is strictly stronger in the full dependent setting. Finally, while AGT provided valuable
intuitions for this work, graduality as embedding-projection pairs was the key technical driver in
the design of CastCIC."

Formatting
* when polishing each chapter do a search to find and replace cruft with macros
* nice looking multi tabbed proof format?
* make rule names conistent, match fonts
* listing the git location and hash
* try to clean up the formalizms with https://users.cs.northwestern.edu/~jesse/code/latex/ottalt/ottalt.pdf
* http://lists.seas.upenn.edu/pipermail/types-list/2019/002163.html

Send to people for review
* Chapter 6.1, Fuzzing person 

## After Defence

last last batch of paperwork https://www.bu.edu/cas/academics/phd-and-mfa-academics/graduation-information/
* Exit survey

post defence paperwork
* http://www.bu.edu/cas/academics/phd-and-mfa-academics/graduation-information/candidate-contact-information-form-for-phd-and-mfa-students/
* PhD Contact Information Form http://www.bu.edu/cas/academics/phd-and-mfa-academics/graduation-information/candidate-contact-information-form-for-phd-and-mfa-students/
* BU Doctoral Exit Survey, Survey of Earned Doctorates
* Attribution CC BY this repo

Fun drinks owed to proof readers:
* Ramsay
* Elise