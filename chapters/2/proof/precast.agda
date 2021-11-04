{-# OPTIONS --allow-unsolved-metas #-} 
module precast where


open import Data.Nat
open import Data.Fin
open import Data.Maybe 
open import Data.List hiding (lookup ; [_])
-- open import Data.Vec hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)


data PreSyntax {n : ℕ} : Set where
  pVar : (i : Fin n) -> PreSyntax {n}
  pTyU : PreSyntax
  
  pCast : (bod : PreSyntax {n})
    -> (uTy : PreSyntax {n})
    -- location, observation
    -> (ty : PreSyntax {n})
    -> PreSyntax {n}

  pPi : PreSyntax {n} -> PreSyntax {suc n} -> PreSyntax
  
  pFun : (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  
  pApp :  PreSyntax {n} -> PreSyntax {n} -> PreSyntax


-- degenerate context extention
extPreSyntax : {i j : ℕ}
  -> (ρ : (Fin i -> Fin j))
  -> Fin (suc i) -> (Fin (suc j))
extPreSyntax ρ zero = zero
extPreSyntax ρ (suc x) = suc (ρ x)


 
postulate
  oo : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}

  _[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}

 -- subst :{n j : ℕ} -> PreSyntax {n} -> (Fin n -> PreSyntax { j}) -> PreSyntax { j}

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
