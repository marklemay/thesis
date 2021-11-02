

module syn where

open import presyntax

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])



--  Ctx  : ℕ -> Set -- assume ctxs were well formed by consnstruction
--  Emp : Ctx 0

data Ctx : {n : ℕ} -> Set
data _|-_::_ {n : ℕ} (Γ : Ctx {n}) : PreSyntax {n}  -> PreSyntax {n} -> Set

-- definitional eq
data  _|-_==_::_ {n : ℕ} (Γ : Ctx {n}) : PreSyntax {n} -> PreSyntax {n} -> PreSyntax {n} -> Set  where
  joinV : {n m m' ty : _}
    -> Γ |- m :: ty
    -> Γ |- m' :: ty
    -> m ~>p* n
    -> m' ~>p* n
    -> Γ |- m == m' :: ty

data Ctx where
  Emp : Ctx {zero}
  Ext : {n : ℕ} {a : PreSyntax {n}} -> (Γ : Ctx) -> Γ |- a :: pTyU -> Ctx {suc n}

postulate
  o : {n : ℕ} {a aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a :: po aTy
    
  o-== : {n : ℕ} {a a' aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a == a' :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a == po a' :: po aTy
  In : {n : ℕ} {ty : PreSyntax {n}} -> (Γ : Ctx) -> (v : Fin n) -> Γ |- ty :: pTyU -> Set 


data _|-_::_ {n} Γ  where
  Var : (v : Fin n) -> {ty : _} -> {Ty : _} -> In {_} {ty} Γ v Ty -> Γ |- pVar v :: ty
  TyU : Γ |- pTyU :: pTyU
  Pi : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> (aTy : Γ  |- aty :: pTyU)
    -> (bodTy : Ext Γ aTy |- bodty :: pTyU)
    -> Γ |-  pPi aty bodty :: pTyU
    
  Fun : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> {bod : PreSyntax }
    -> (aTy : Γ  |- aty :: pTyU)
    -> (bodTy : Ext Γ aTy |- bodty :: pTyU)
    -> Ext (Ext Γ aTy)  (o (Pi aTy bodTy)) |- bod :: po bodty
    -> Γ |- pFun bod :: pPi aty bodty
    
  App : {f a aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |-  f  :: pPi aTy bodTy -> Γ  |- a :: aTy 
    -> Γ |-  pApp f a  :: (bodTy [ a ])
  Cast : {e : PreSyntax } -> {ty : PreSyntax }
    -> Γ |-  e :: ty
    -- -> Γ |-  ty :: pTyU
    -> Γ |-  pAnn e ty  :: ty
    

  Conv : {a m m' : PreSyntax }
    -> Γ |-  a  :: m
    -> Γ |- m == m' :: pTyU
    -> Γ |-  a  :: m'


--postulate
--  ok :  {n : ℕ} {Γ : PreCtx n} {a aTy : _} -> Γ |- a :: aTy -> Ctx {_} {Γ}
--  lookup :  {n : ℕ} {Γ : PreCtx n} -> (Ctx  {_} {Γ}) -> Fin n -> Σ _ \ aTy -> Γ |- aTy :: pTyU

