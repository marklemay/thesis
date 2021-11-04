module bidir where

open import presyntax

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

-- untyped definitional eq
data  _~~_ {n : ℕ} : PreSyntax {n} -> PreSyntax {n} -> Set where
  joinV : {n m m' : _}
    -> m ~>p* n
    -> m' ~>p* n
    -> m ~~ m'

--  Ctx  : ℕ -> Set -- assume ctxs were well formed by consnstruction
--  Emp : Ctx 0


-- data Ctx : {n : ℕ} -> Set
data _|-_:<-:_ {n : ℕ} (Γ : pCtx {n}) : PreSyntax {n} -> PreSyntax {n} -> Set
data _|-_:->:_ {n : ℕ} (Γ : pCtx {n}) : PreSyntax {n} -> PreSyntax {n} -> Set

{-
-- in agda it makes sense to work in mutially well formed contexts
data Ctx where
  Emp : Ctx {zero}
  Ext : {n : ℕ} {a : PreSyntax {n}} -> (Γ : Ctx) -> Γ |- a :<-: pTyU -> Ctx {suc n}

data WFCtx : {n : ℕ} -> pCtx {n} -> Ctx {n} -> Set where
  EmpWF : WFCtx pEmp Emp
  ExtWF : {n : ℕ} {Γ : _} {H : _} {a : PreSyntax {n}}
    -> WFCtx H Γ
    -> (awf : Γ |- a :<-: pTyU)
    -> WFCtx (pExt H a) (Ext Γ awf)
-}


CtxOK : {n : ℕ} -> (Γ : pCtx {n}) -> Set
CtxOK Γ = (v : _) -> (ty : _ ) -> In Γ v ty -> Γ |- ty :<-: pTyU




data _|-_:->:_ {n} Γ  where
  Var : CtxOK  Γ
    -> (v : Fin n) -> {ty : _}
    --  -> {Ty : _} -> In {_} {ty} Γ v Ty ->
    -> In Γ v ty
    -> Γ |- pVar v :->: ty
  TyU : CtxOK  Γ
    -> Γ |- pTyU :->: pTyU
  Ann : {e : PreSyntax } -> {ty : PreSyntax }
    -> Γ |-  ty :<-: pTyU
    -> Γ |-  e :<-: ty
    -> Γ |-  pAnn e ty :->: ty
  Pi : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> (aTy : Γ  |- aty :<-: pTyU)
    -> (bodTy : pExt Γ aty |- bodty :<-: pTyU)
    -> Γ |-  pPi aty bodty :->: pTyU
  App : {f a aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |- f :->: pPi aTy bodTy
    -> Γ |- a :<-: aTy 
    -> Γ |- pApp f a  :->: (bodTy [ a ])
    
data _|-_:<-:_ {n} Γ  where
  Fun : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> {bod : PreSyntax }
    -> (aTy : Γ  |- aty :<-: pTyU)
    -> (bodTy : pExt Γ aty |- bodty :<-: pTyU)
    -> pExt (pExt Γ aty)  (po (pPi aty bodty)) |- bod :<-: po bodty
    -> Γ |- pFun bod :<-: pPi aty bodty
    -- TODO discuss that funs take types that are not directly convertable, and thus require annotations
    -- thjis is standard as per https://www.cl.cam.ac.uk/~nk480/bidir-survey.pdf (Coqrand whnfed it)
    -- the implementation is more libral and will atempt to evaluate to WHNF
    
  Conv : {a m m' : PreSyntax }
    -> Γ |- a :->: m
    -> m ~~ m'
    -> Γ |- m' :<-: pTyU
    -> Γ |- a :<-: m'
    
{-
TODO
 well typed
 regularity
 conservative
-}
