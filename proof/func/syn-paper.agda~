

module syn-paper where

open import presyntax

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

-- do things the in a way that makes less sense in agda but is more readable on paper

  
-- definitional eq
data _~~_ {n : ℕ} : PreSyntax {n} -> PreSyntax {n} -> Set  where
  joinV : {n m m' : _}
    -> m ~>p* n
    -> m' ~>p* n
    -> m ~~ m'

data _|-_::_ {n : ℕ} (Γ : pCtx {n}) : PreSyntax {n}  -> PreSyntax {n} -> Set


CtxOK : {n : ℕ} -> (Γ : pCtx {n}) -> Set
CtxOK Γ = (v : _) -> (ty : _ ) -> In Γ v ty -> Γ |- ty :: pTyU

data _|-_::_ {n} Γ  where
  Var : (v : Fin n) -> {ty : _} -> In {_} Γ v ty -> Γ |- pVar v :: ty
  TyU : Γ |- pTyU :: pTyU
  Pi : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> (aTy : Γ  |- aty :: pTyU)
    -> (bodTy : pExt Γ aty |- bodty :: pTyU)
    -> Γ |-  pPi aty bodty :: pTyU
    
  Fun : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> {bod : PreSyntax }
    -- -> (aTy : Γ  |- aty :: pTyU)
    -- -> (bodTy : pExt Γ aTy |- bodty :: pTyU)
    -> pExt (pExt Γ aty)  (po (pPi aty bodty)) |- bod :: po bodty
    -> Γ |- pFun bod :: pPi aty bodty
    
  App : {f a aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |- f :: pPi aTy bodTy
    -> Γ |- a :: aTy 
    -> Γ |- pApp f a :: (bodTy [ a ])
    
  Ann : {e : PreSyntax } -> {ty : PreSyntax }
    -> Γ |-  e :: ty
    -- -> Γ |-  ty :: pTyU
    -> Γ |-  pAnn e ty  :: ty
    
  Conv : {a m m' : PreSyntax }
    -> Γ |-  a  :: m
    -> m ~~ m'
    -> Γ |-  a  :: m'

