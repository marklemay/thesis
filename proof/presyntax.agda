{-# OPTIONS --allow-unsolved-metas #-} 
module presyntax where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec   hiding (lookup ; [_])
open import Data.Product hiding (map)

-- TODO remove Pre- p- prefexes and enocourage imports

data PreSyntax {n : ℕ} : Set
data PreSyntax {n} where
  pVar : (i : Fin n) -> PreSyntax
  pTyU : PreSyntax
  pPi :  (aTy : PreSyntax {n}) -> (bodTy :  PreSyntax {suc n}) -> PreSyntax
  pFun : (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  pApp :  (f : PreSyntax {n}) -> (a : PreSyntax {n}) -> PreSyntax
  pAnn :  (e : PreSyntax {n}) -> (ty : PreSyntax {n}) -> PreSyntax

postulate
  extPreSyntax : {i j : ℕ}
    -> (ρ : (Fin i -> Fin j))
    -> Fin (suc i) -> (Fin (suc j))
 
renamePreSyntax : {i j : ℕ}
  -> (ρ : (Fin i -> Fin j))
  -> (PreSyntax {i} -> PreSyntax {j})
renamePreSyntax ρ (pVar i) = pVar (ρ i)
renamePreSyntax ρ pTyU = pTyU
renamePreSyntax ρ (pPi aTy bodTy) = pPi (renamePreSyntax ρ aTy) (renamePreSyntax (extPreSyntax ρ) bodTy)
renamePreSyntax ρ (pFun bod)
  = pFun ((renamePreSyntax (extPreSyntax (extPreSyntax ρ)) bod))
renamePreSyntax ρ (pApp f a) = pApp (renamePreSyntax ρ f) (renamePreSyntax ρ a)
renamePreSyntax ρ (pAnn e ty) = pAnn (renamePreSyntax ρ e) (renamePreSyntax ρ ty)

po : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}
po = renamePreSyntax (raise 1)

postulate
  substPreSyntax : ∀ {i j}
    → (σ : (Fin i → PreSyntax {j} ))
    → (PreSyntax {i}  → PreSyntax {j})


_[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}
_[_] {n} pTyU withThis = pTyU
_[_] {n} inthis withThis = substPreSyntax {suc n} {n} σ inthis
  where
    σ : Fin (suc n) → PreSyntax {n}
    σ zero = withThis
    σ (suc x) = pVar x


data pCtx : {n : ℕ} -> Set where
  pEmp : pCtx {zero}
  pExt : {n : ℕ} -> (Γ : pCtx {n}) -> (a : PreSyntax {n}) -> pCtx {suc n}

postulate
  In : {n : ℕ} -> (Γ : pCtx {n}) -> (v : Fin n) -> (ty : PreSyntax {n})  -> Set

postulate
--  pLookup : {n : ℕ} (Γ : pCtx n) -> (i : Fin n)  -> PreSyntax {n}
  _[_::=_] :{n : ℕ} -> PreSyntax {suc n} -> (i : Fin n) -> PreSyntax {n} -> PreSyntax {n}
    
data _~>p_ {n : ℕ} : PreSyntax {n}  -> PreSyntax {n} -> Set  where
  par-red : {a a' : _} -> {bod bod' : _ }
    -> (a-a' : a ~>p a')
    -> (bod-bod' : bod ~>p bod')
    -> (pApp (pFun bod)  a) ~>p ( bod' [ po (pFun bod') ] [ a' ]  )

  par-cast-red : {e e' : PreSyntax} -> {ty : PreSyntax}
    ->  e ~>p e' 
    -> (pAnn e ty) ~>p e'
    
  -- structural

  par-Var : {i : Fin n}
    -> (pVar i) ~>p pVar i
    
  par-TyU : pTyU ~>p pTyU
    
  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> (pPi aTy bodTy) ~>p pPi aTy' bodTy'
    
  par-Fun :
    {bod bod' : _}
    -> bod ~>p bod'
    -> (pFun bod) ~>p pFun bod'
    
  par-App : {f f' a a' : _}
    -> f ~>p f'
    -> a ~>p a'
    -> (pApp f a) ~>p (pApp f' a')

  par-cast : {e e' : PreSyntax} -> {ty ty' : PreSyntax}
    ->  e ~>p e' 
    ->  ty ~>p ty' 
    -> (pAnn e ty) ~>p (pAnn e' ty')

par-refll : {n : ℕ}  (a : PreSyntax {n}) -> a ~>p a
par-refll (pVar i) = par-Var
par-refll pTyU = par-TyU
par-refll (pPi x x₁) = par-Pi (par-refll x) (par-refll x₁)
par-refll (pFun x) = par-Fun (par-refll x)
par-refll (pApp x x₁) = par-App (par-refll x) (par-refll x₁)
par-refll (pAnn x x₁) = par-cast (par-refll x) (par-refll x₁)

-- very influenced by https://plfa.github.io/Confluence/#parallel-reduction-satisfies-the-diamond-property
-- misleading name
-- the way this is presented, par-max may not be par, but instead withinexactly 2 par reductions away
par-max : {n : ℕ} -> PreSyntax {n} -> PreSyntax {n} 
par-max (pApp f@(pFun bod) a) = (par-max bod) [ po (par-max f) ] [ par-max a ]
par-max (pApp f a) = pApp (par-max f) (par-max a)
par-max (pVar i) = pVar i
par-max pTyU = pTyU
par-max (pPi aTy bodTy) = pPi (par-max aTy) (par-max bodTy)
par-max (pFun bod) = pFun (par-max bod)
par-max (pAnn e ty) = par-max e
    
postulate
  sub-par : {n : ℕ} {a a' : PreSyntax {suc n}} {b b' : PreSyntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> (a [ b ] ) ~>p  (a' [ b' ])

  po-par : {n : ℕ} {a a' : PreSyntax { n}} 
      -> a ~>p  a'
      -> po a ~>p  po a'

-- annoying name
par-triangle :  {n : ℕ} {a b : PreSyntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
par-triangle (par-red par-arg par-bod)
  = sub-par (sub-par (par-triangle par-bod) (po-par (par-triangle (par-Fun par-bod)))) (par-triangle par-arg)
par-triangle (par-App  (par-Fun par-f) par-a)
  = par-red (par-triangle par-a) (par-triangle par-f)
par-triangle (par-cast-red par-e) = par-triangle par-e
par-triangle par-Var = par-Var
par-triangle par-TyU = par-TyU
par-triangle (par-Pi par-aTy par-bodTy) = par-Pi (par-triangle par-aTy) (par-triangle par-bodTy)
par-triangle (par-Fun par-bod) = par-Fun (par-triangle par-bod)
par-triangle (par-cast par-e _) = par-cast-red (par-triangle par-e)

-- applications spelled out, someday replace with 
-- par-triangle (par-App par-f par-a) = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-red x x₁) par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-cast-red x) par-a)
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-Var par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-TyU par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-Pi x x₁) par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-App x x₁) par-a)
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-cast x x₁) par-a)
  = par-App (par-triangle par-f) (par-triangle par-a)

confulent-~> : {n : ℕ} {a b b' : PreSyntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
confulent-~>  {_} {a} ab ab' = par-max a , par-triangle ab , par-triangle ab'


-- typed transitive reflective closuer
data _~>p*_ {n : ℕ}  : PreSyntax {n}  -> PreSyntax {n} -> Set  where
  par-refl : {m : _} -> m ~>p* m      -- TODO this could be admissable
    
  par-step : {a b c : _}
    -> a ~>p* b
    -> b ~>p c
    -> a ~>p* c

-- TODO is the strip lemma acuatlly needed or is it just an artifact of the encoding? not exactly
-- implicit is that the recursive result will preserve the dimension of tiles,  a single confluent step will wland within 1 step ot the corner
-- alternatively build up the tiling fronteer explicitly,
-- m : PreSyntax {n} -> ls : [a,m ~>p* a] -> exists v forall a <- fst ls, a ~>p* v
confulent-~>p* : {n : ℕ}  {m a a' : PreSyntax {n}}
   -> m ~>p* a
   -> m ~>p* a'
   -> Σ _ \ v  -> a ~>p* v × a' ~>p* v
confulent-~>p* {_} {m} {.m} {a'} par-refl ma' = a' , ma' , par-refl
confulent-~>p* {_} {m} {a} {.m}  ma par-refl = a , par-refl , ma
confulent-~>p* {_} {m} {a} {a'} (par-step m*b ba) (par-step m*b' b'a') = {!!}

{-
data WHNF {n : ℕ}  : PreSyntax {n} -> Set  where
  whnf : 
-}
