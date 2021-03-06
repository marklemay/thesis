{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-} 
module precast where


open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Maybe 
open import Data.Bool 
import Data.List -- hiding (lookup ; [_])
open import Data.Vec hiding (lookup ; [_] ) -- ; insert)
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)


postulate
  Loc : Set

{-# NO_UNIVERSE_CHECK #-}
record D : Set where
--  constructor ~_,_,_,_~
  field
    var : ℕ
    tCon : ℕ
    con : ℕ
    pathV : ℕ
    sepV : ℕ
     --TODO Spine lengths should live here?
    
--    
--    nulLoc : Loc

bind : ℕ -> D -> D
bind x d = record d {var = (x + D.var d)  }


bindsep : ℕ -> D -> D
bindsep x d = record d {var = (x + D.var d)  }

unseperate : D -> D
unseperate x = record x {sepV = 0 }


fixChoice : (d : D) -> (i : Fin (D.sepV d)) -> D
fixChoice = λ d i →  record d {sepV = (Data.Nat.pred (D.sepV d)) }

{-
data choiceTree (A : Set) : (n : ℕ) -> Set where
  Just : A -> choiceTree A 0
  choice : {n : _} -> choiceTree A n -> choiceTree A n -> choiceTree A (suc n)

-- This is what I want, but hard to work with definitionally
ChoiceTree : {A : Set} -> {n : ℕ} -> Set
ChoiceTree {A} {n} = Vec Bool n -> A
-}



--postulate
--  ChoiceF

data PreSyntax {d : D} : Set


ChoiceTree : {D} -> Set
ChoiceTree {d} = Vec Bool (D.sepV d) -> PreSyntax {unseperate d}


data Obs {d : D} : Set where
  here :  Obs
  InTC :  ℕ -> Obs
-- ...

data PrePath {d : D} : Set where
  PVar : (i : Fin (D.pathV d)) -> PrePath
  Assert : (a a' : PreSyntax {d})
    -> PrePath
    
  Refl : PrePath
  Trans : PrePath {d} -> PrePath {d} -> PrePath {d}
  Rev : PrePath {d} -> PrePath {d}
  
  InTC : ℕ -> PrePath {d} -> PrePath {d} --TODO as Fin?
  InC : ℕ -> PrePath {d} -> PrePath {d}
  
 -- InFunTyArg : PrePath {d} -> PrePath {d}
 -- InFunTyBod : PrePath {d} -> PrePath {d}
  
  UncastL : PrePath {d} -> PrePath {d}
  UncastR : PrePath {d} -> PrePath {d}


data PrePat {d} : Set where
  patVar : PrePat
  patCon : (i : Fin (D.var d))
    -> Data.List.List (PrePat {d})
    -- and a pathVar!
    -> PrePat

bindPats :  (d : D) -> {i :  _} -> (Vec (PreSyntax {d}) i) -> D
bindPats = {!!}

data PreSyntax {d} where
  Var : (i : Fin (D.var d)) -> PreSyntax
  TCon : (i : Fin (D.tCon d)) -> PreSyntax
  Con : (i : Fin (D.con d)) -> PreSyntax

  Case : {i :  _}
    -> (scruts : Vec (PreSyntax {d}) i)
    -- TAS motive?
    -> Data.List.List ( Σ (Vec (PreSyntax {d}) i) λ p → PreSyntax {bindPats d p} )
    -> {Loc}
  --  -> Data.List.List (Vec (PreSyntax {d}) i)
    -> PreSyntax
  Blame : PrePath {d} -> PreSyntax
  Cast : (bod : PreSyntax {d})
    -- -> (uty : PreSyntax {d}) -- need to explicitly track these, since they are needed to block untyped computation.  specifically functions applied to pi types
    -> ChoiceTree {d}
    -- -> (ty : PreSyntax {d})
    -> PreSyntax
  
  TyU : PreSyntax
  
  Pi : PreSyntax {d} -> PreSyntax {bind 1 d} -> PreSyntax
  Fun : (bod : PreSyntax {bind 2 d}) -> PreSyntax
  
  App :  PreSyntax {d} -> PreSyntax {d} -> PreSyntax
  
  Same : (i : Fin (D.sepV d)) -> PreSyntax {fixChoice d i} -> PreSyntax {fixChoice d i}
    -> Loc -> Obs {d}
    -> PreSyntax


{-
data IsTCSpine {d} : PreSyntax {d} -> Fin (D.tCon d) -> {numArgs : _} -> Vec (PreSyntax {d}) numArgs -> Set where

data PreTelUnit {d : D} : {n : ℕ} -> Set where

data PreTel {d : D} : (D -> Set) -> Set where
-}

postulate
  o : {n : ℕ} {d : D} -> PreSyntax {d} -> PreSyntax {bind 1 d}

  _[_] : {d : D} -> PreSyntax {bind 1 d} -> PreSyntax {d} -> PreSyntax {d}

  --TODO sketchyest def
  -- a partition of pts
  EndPoints : {d : D} -> ChoiceTree {d}
    -> {!!}
    -> {!!}

  -- can "cheat" byforcing an arbitrary order
  EndPoint : {d : D} -> ChoiceTree {d}
    -> ChoiceTree {d}
    -> Vec Bool (D.sepV d)
    -> PreSyntax {unseperate d}
    -> PreSyntax {unseperate d}
    -> Set

  -- build in the suc
 -- insert : {n : ℕ} -> Vec Bool n -> Fin n -> Bool -> Vec Bool (suc n)

  
  single : {d : D} -> Vec Bool (D.sepV d) -> PrePath {unseperate d} -> ChoiceTree {d}

  
  veiw : {d : D} -> Vec Bool (D.sepV d) -> PreSyntax {d} -> PreSyntax {unseperate d}
-- \Rrightarrow not great in this font

-- figure out typeclasses?

-- TODO put in another module for namespacing?

data _⇛path_ {d : D} : PrePath {d} -> PrePath {d} -> Set


data _⇛paths_ {d : D} : ChoiceTree {d} -> ChoiceTree {d} -> Set where
  reflHack : {a : _}
   -> a ⇛paths a
  
data _⇛_ {d : D} : PreSyntax {d} -> PreSyntax {d} -> Set where

  
  App-fun-red : {!!}
  
  App-cast-red : {!!}

  -- need to combine these rules for par red reasons? or strictly order it
  Same-lCast-red :
    {l l' : _}
    -> l ⇛ l'
    -> {r r' : _}
    -> r ⇛ r'
    -> {ii : _} {ps p : _} {ll rr : _}
    -> EndPoint ps p ii ll rr
    -> {p' : _} 
    -> p ⇛paths p'
    -> {ll' : _}
    -> ll ⇛ ll'
    -> {rr' : _}
    -> rr ⇛ rr'
    -> {i : Fin (D.sepV d)} {loc : Loc} {o : Obs {d}}
    -> Same i (Cast l ps) r loc o ⇛  Cast (Same i (Cast l' p') r' loc o) let temp = single (insert ii {!i!} true) (Assert ? ? ) -- (veiw { record d {sepV = {!!} }} ii {!ll'!}) {!!})
         in {!!} 

  Same-rCast-red : {!!}

  Same-TyU-red :  {i : Fin (D.sepV d)} {l : Loc} {o : Obs {d}}
    -> Same i TyU TyU l o ⇛ TyU
  
  Same-data-ty-red : {!!}
  
  Same-data-cons-red : {!!}
  
  Same-pi-red : {!!}

  Same-fun-red : {!!}
  -- needs to multistep
  cast-trans-red : {!!}
  
  cast-refl-red : {!!}
  
  
-- structural rules

  Blame : {p p' : _}
    -> p ⇛path p'
    -> Blame p ⇛ Blame p'
{-
  Cast :
    {b b' : _}
    -> b ⇛ b'
    ->{uty uty' : _}
    -> uty ⇛ uty'
    ->{ty ty' : _}
    -> ty ⇛ ty'
    
    ->{p p' : _}
    -> p ⇛path p'
    -> Cast b uty p ty ⇛ Cast b' uty' p' ty'
-}
  Pi :
    {a a' : _}
    -> a ⇛ a'
    ->{b b' : _}
    -> b ⇛ b'
    -> Pi a b ⇛ Pi a' b'

  -- ...

  reflHack : {a : PreSyntax {d}} --it may be possible to actually use this as the definition
    -> a ⇛ a
  


data _⇛Obs_ {d : D} : Obs {d} -> Obs {d} -> Set where

  reflHack : {a : Obs {d}}
    -> a ⇛Obs a
  

data _⇛path_ {d} where

{-
  Assert-red-TC : {tc : Fin (D.tCon d)} -> {numArgs : _} -- TODO restrict to fully applied
    -> {l : PreSyntax {d}}
    -> {largs : Vec (PreSyntax {d}) numArgs } 
    -> IsTCSpine l tc largs

    -> {r : PreSyntax {d}}
    -> {rargs : Vec (PreSyntax {d}) numArgs } 
    -> IsTCSpine r tc rargs

    -> {loc : Loc}
    -> {o o' : Obs}
    -> {c c' : _}
    -- largs ⇛ largs'
    -- rargs ⇛ rargs'
    -- zip and rebind args as assertions with observations
    
    -> Assert l r loc o c ⇛path {!!}
-}

-- structural rules

{-
  Assert : {a a' b b' : PreSyntax {d}} 
    -> a ⇛ a'
    -> b ⇛ b'
    -> {o o' : Obs}
    -> o ⇛Obs o'
    -> {c c' : PreSyntax {bind 1 d}}
    -> c ⇛ c'
    -> {l : Loc} 
    -> Assert a b l o c ⇛path Assert a' b' l o' c'
-}

  reflHack : {a : PrePath {d}}
   -> a ⇛path a
  
{-


 -- subst :{n j : ℕ} -> PreSyntax {n} -> (Fin n -> PreSyntax { j}) -> PreSyntax { j}

{-

o : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}
o pTyU = pTyU -- helpful if ithi is definitional
o x = oo x


-- TODO: everything below should be revised

{-
  sub-in-place :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {suc n} -> PreSyntax {suc n}
  
  _~:~_ : {n : ℕ} -> PreSyntax {n} -> List (PreSyntax {n}) -> PreSyntax {n}

data  _~>peq_ {n : ℕ}: List (PreSyntax {n})  -> List (PreSyntax {n}) -> Set

data allPi {n : ℕ} :  List (PreSyntax {n}) -> List (PreSyntax {suc n}) -> Set  where
  all-is-emp : allPi [] []
  pi2-cons : {aTy : _} -> {bodTy : _} ->
    {input  : _} -> {out : _} ->
    allPi input out -> allPi (pPi2 aTy bodTy ∷ input) (bodTy  ∷  Data.List.map (λ bty → sub-in-place bty (pCast (pVar zero) ( o aTy  ∷  []))) out)
-}

{-
data _~>p_ {n : ℕ} : PreSyntax {n}  -> PreSyntax {n} -> Set  where

  par-app-red : {a a' : _} -> {bod bod' : _ }
    -> a ~>p a'
    -> bod ~>p bod'
    -> pApp (pFun bod) a
         ~>p ((( (bod' [ o (pCast (pFun bod') fcasts') ])  ~:~ bodcasts' ) [ a' ]) ~:~ casts')


  par-red : {a a' : _} -> {bod bod' : _ } -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> a ~>p a'
    -> bod ~>p bod'
    -> {fcasts fcasts' : _} {bodcasts bodcasts' : _}
    -> fcasts ~>peq fcasts'
    -> allPi fcasts bodcasts
    -> bodcasts ~>peq bodcasts'
    ->  pCast (pApp (pCast (pFun bod) fcasts)  a) casts
         ~>p ((( (bod' [ o (pCast (pFun bod') fcasts') ])  ~:~ bodcasts' ) [ a' ]) ~:~ casts')

  -- structural
  par-Var : {i : Fin n} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> (pCast (pVar i) casts) ~>p (pCast (pVar i) casts')

  par-TyU2 : (pTyU2) ~>p pTyU2

  par-Pi2 : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> (pPi2 aTy bodTy) ~>p pPi2 aTy' bodTy'

  par-Fun : 
    {bod bod' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> bod ~>p bod'
    -> pCast (pFun bod) casts ~>p pCast (pFun  bod') casts'

  par-App : {f f' a a' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> f ~>p f'
    -> a ~>p a'
    -> pCast (pApp f a) casts ~>p pCast (pApp f' a') casts'
{-
  par-TyU : {casts casts' : List (PreSyntax {n})} -> casts ~>peq casts'
    -> (pCast pTyU casts) ~>p (pCast pTyU casts')
    
  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _} -> {casts casts' : List (PreSyntax {n})}  -> casts ~>peq casts'
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> pCast  (pPi aTy bodTy) casts ~>p pCast (pPi aTy' bodTy') casts'
-}

data  _~>peq_ {n}  where
  par-emp : [] ~>peq []
  par-cons :  {a a' : _} {rest rest' : _} 
    -> a ~>p a'
    -> rest ~>peq rest'
    -> (a ∷ rest) ~>peq (a' ∷ rest')

par-eq-refll : {n : ℕ}  (a : List (PreSyntax {n})) -> a ~>peq a

par-refll : {n : ℕ}  (a : PreSyntax {n}) -> a ~>p a
par-refll (pCast (pVar i) eqs) = par-Var (par-eq-refll eqs)
par-refll (pCast (pFun bod) eqs) = par-Fun (par-eq-refll eqs) (par-refll bod)
par-refll (pCast (pApp x x₁) eqs) = par-App (par-eq-refll eqs) (par-refll x) (par-refll x₁)
par-refll pTyU2 = par-TyU2
par-refll (pPi2 a a₁) = par-Pi2 (par-refll a) (par-refll a₁)

par-eq-refll [] = par-emp
par-eq-refll (x ∷ a) = par-cons (par-refll x) (par-eq-refll a)

postulate
  sub-par : {n : ℕ} {a a' : PreSyntax {suc n}} {b b' : PreSyntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> (a [ b ] ) ~>p  (a' [ b' ])
    
  o-par : {n : ℕ} {a a' : PreSyntax { n}} 
      -> a ~>p  a'
      -> o a ~>p  o a'

  ~:~-par : {n : ℕ} {a a' : PreSyntax { n}}  {b b' : List (PreSyntax {n})}
      -> a ~>p  a'  -> b ~>peq  b'
      -> (a ~:~ b) ~>p  (a' ~:~ b')
      
  allPi-par : {n : ℕ} {a a' : _}  {b b' : _}
      -> a ~>peq  a'  -> b ~>peq  b'
      -> (allPi {n} a b) -> (allPi {n} a' b')

-- TOOD bettername par-red?
par-red-max :  {n : ℕ} -> List (PreSyntax {n}) -> Maybe (List (PreSyntax {suc n}))

par-eq-max : {n : ℕ} -> List (PreSyntax {n}) -> List (PreSyntax {n})

par-max : {n : ℕ} -> PreSyntax {n} -> PreSyntax {n}
par-max (pCast (pApp (pCast (pFun bod) feqs) a) eqs) with par-red-max feqs
-- par-max (pCast (pApp f@(pCast (pFun bod) feqs) a) eqs) | just bodeqs = (((par-max bod [ o (par-max f) ]) ~:~ par-eq-max bodeqs)  [ par-max a ]) ~:~ par-eq-max eqs
par-max (pCast (pApp f@(pCast (pFun bod) feqs) a) eqs) | just bodeqs = (((par-max bod [ o (par-max f) ]) ~:~ bodeqs)  [ par-max a ]) ~:~ par-eq-max eqs
par-max (pCast (pApp f a) eqs) | nothing = pCast (pApp (par-max f) (par-max a)) (par-eq-max eqs)
par-max (pCast (pApp f a) eqs) = pCast (pApp (par-max f) (par-max a)) (par-eq-max eqs)
par-max (pCast (pVar i) eqs) = pCast (pVar i) (par-eq-max eqs)
par-max (pCast (pFun bod) eqs) = pCast (pFun (par-max bod)) (par-eq-max eqs)
par-max pTyU2 = pTyU2
par-max (pPi2 aTy bodTy) = pPi2 (par-max aTy) (par-max bodTy)

par-eq-max [] = []
par-eq-max (a ∷ rest) = (par-max a)  ∷ par-eq-max rest

par-red-max [] = just [] -- TODO: insert arg cast
par-red-max ((pPi2 aTy bodTy) ∷ rest) with par-red-max rest
par-red-max (pPi2 aTy bodTy ∷ rest) | just rest' = just ((par-max bodTy) ∷ Data.List.map (λ bty → sub-in-place bty (pCast (pVar 0F) ( o (par-max aTy)  ∷  []))) rest') -- TODO: insert arg cast
par-red-max (pPi2 aTy bodTy ∷ rest) | nothing = nothing
par-red-max _ = nothing

par-red-max-ok :  {n : ℕ}  {fcast : _}  {bodcast : _} -> allPi {n} fcast bodcast -> par-red-max fcast ≡ just (par-eq-max bodcast) -- fragile
par-red-max-ok all-is-emp = refl
par-red-max-ok (pi2-cons x) rewrite par-red-max-ok x = {!!} --correct, but non tirvial to proove

{-
allPi? :  {n : ℕ}  (fcast : _) ->
  ( Σ _ λ bodcast → allPi {n} fcast bodcast) -- TODO also unique
  ⊎ ¬ ( (bodcast : _) -> allPi {n} fcast bodcast) 
allPi? [] = inj₁ ([] , all-is-emp)
allPi? ((pPi2 aTy bodTy) ∷ fcast) with allPi? fcast
allPi? (pPi2 aTy bodTy ∷ fcast) | inj₁ (fst , snd) = inj₁ (bodTy ∷ fst , pi2-cons snd) 
allPi? (pPi2 aTy bodTy ∷ fcast) | inj₂ y = inj₂ {!!} -- ok
allPi? (_  ∷ fcast)  = inj₂ {!!} -- ok
-}
par-eq-triangle :  {n : ℕ} {a b : List (PreSyntax {n})}
   -> a ~>peq b
   -> b ~>peq (par-eq-max a)
   
par-triangle :  {n : ℕ} {a b : PreSyntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)

{-# TERMINATING #-}
par-red-triangle :  {n : ℕ}  (fcast : _)
  -> (par-red-max fcast ≡ nothing)
  ⊎ Σ _ λ bodcast → (par-red-max fcast ≡ just (par-eq-max bodcast)) × allPi {n} fcast bodcast × ({fcast' : _} -> fcast ~>peq fcast' ->  Σ _ λ bodcast' → allPi {n} fcast' bodcast' × (bodcast' ~>peq par-eq-max bodcast) )
  -- better as 2 lemmas? would make temination checking more possible
par-red-triangle [] = inj₂ ([] , (refl , (all-is-emp ,  xx)))
  where
    xx :  {fcast' : _} -> [] ~>peq fcast' -> Σ (List PreSyntax) (λ z → Σ (allPi fcast' z) (λ _ → z ~>peq []))
    xx par-emp = [] , all-is-emp , par-emp 
par-red-triangle ((pPi2 aTy bodTy) ∷ fcast) with par-red-triangle fcast
par-red-triangle (pPi2 aTy bodTy ∷ fcast) | inj₂ (bodcast , eq , allPi-fcast-bodcast , max) rewrite eq
  = inj₂ (bodTy ∷ Data.List.map (λ z → sub-in-place z (pCast (pVar 0F) (o aTy ∷ [])))  bodcast
    , ({!!} , ( pi2-cons allPi-fcast-bodcast
  ) , xx))
  where
    xx : {fcast' : _} → (pPi2 aTy bodTy ∷ fcast) ~>peq fcast'
      →  Σ _ (λ bodcast' →  (allPi fcast' bodcast')
          × (bodcast' ~>peq (par-max bodTy ∷
             par-eq-max
             (Data.List.map
              (λ z → sub-in-place z (pCast (pVar 0F) (o aTy ∷ []))) bodcast))))
    xx (par-cons (par-Pi2 par-aty par-bodty) rest) with max rest
    xx (par-cons (par-Pi2 par-aty par-bodty) rest) | bodcast' , allPi-rest'-bodcast' , to-max = _ , ((pi2-cons allPi-rest'-bodcast') , par-cons (par-triangle par-bodty) {!!}) -- looks correct...

par-red-triangle (pPi2 aTy bodTy ∷ fcast) | inj₁ x = inj₁ {!!} -- ok
par-red-triangle (_ ∷ fcast) = inj₁ {!!} -- ok


-- par-triangle (par-red par-casts par-arg par-bod fcasts bodcasts all-pi) with allPi?-max fcasts
-- fcasts bodcasts bodcasts'
par-triangle (par-red par-casts par-arg par-bod {fcasts} par-fcasts all-pi par-bodcasts) rewrite par-red-max-ok all-pi
  = ~:~-par (sub-par (~:~-par (sub-par
    (par-triangle par-bod)
    (o-par (par-Fun (par-eq-triangle par-fcasts)
    (par-triangle par-bod))))
    (par-eq-triangle par-bodcasts))
    (par-triangle par-arg))
    (par-eq-triangle par-casts)

par-triangle (par-App par-casts (par-Fun {_} {_} {fcasts} par-fcasts par-bod) par-a) with par-red-triangle fcasts
par-triangle (par-App par-casts (par-Fun {_} {_} {fcasts} {fcasts'} par-fcasts par-bod) par-a) | inj₂ (bodcast , eq , fst , snd) rewrite eq with snd par-fcasts
... | max-bodcast' , allPi-f , par-bodcast   = par-red (par-eq-triangle par-casts) (par-triangle par-a) (par-triangle par-bod) (par-eq-triangle par-fcasts) allPi-f par-bodcast
-- par-f sillyness {
par-triangle (par-App par-casts par-f@(par-Fun {_} {_} {fcasts} par-fcasts par-bod) par-a) | inj₁ x rewrite x
  = par-App (par-eq-triangle par-casts) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-casts par-f@(par-red x x₁ x₂ x₃ x₄ x₅) par-a) 
  = par-App (par-eq-triangle par-casts) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-casts par-f@(par-Var x) par-a) 
  = par-App (par-eq-triangle par-casts) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-casts par-f@par-TyU2 par-a) 
  = par-App (par-eq-triangle par-casts) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-casts par-f@(par-Pi2 x x₁) par-a) 
  = par-App (par-eq-triangle par-casts) (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-casts par-f@(par-App x x₁ x₂) par-a) 
  = par-App (par-eq-triangle par-casts) (par-triangle par-f) (par-triangle par-a)
-- }
par-triangle (par-Var par-casts) = par-Var (par-eq-triangle par-casts)
par-triangle (par-Fun par-casts par-bod) = par-Fun (par-eq-triangle par-casts) (par-triangle par-bod)
par-triangle par-TyU2 = par-TyU2
par-triangle (par-Pi2 x x₁) = par-Pi2 (par-triangle x) (par-triangle x₁)

par-eq-triangle par-emp = par-emp
par-eq-triangle (par-cons x xs) = par-cons (par-triangle x) (par-eq-triangle xs)

confulent-~> : {n : ℕ} {a b b' : PreSyntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
confulent-~> {_} {a} ab ab' = (par-max a) , (par-triangle ab) , par-triangle ab'

{-
-}
{-
data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU2 : pTyU2 val
  vPi2 : { aTy : PreSyntax } -> {bodTy : PreSyntax }
     -> (pPi2 aTy bodTy) val
  -- ..
-}
-}

-}
-}
