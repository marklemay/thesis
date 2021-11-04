module cast where

open import precast

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



data Ctx where
  Emp : Ctx {zero}
  Ext : {n : ℕ}  -> (Γ : Ctx)
    -> (a : PreSyntax {n}) -- use untyped ctx, silly in agda , but makes pencil-paper inducitonscleaner
    -- -> {a : PreSyntax {n}}
    -- -> Γ |- a :: pTyU
    -> Ctx {suc n}



postulate
  -- definitional eq
  _~~_ : {n : ℕ} -> PreSyntax {n} -> PreSyntax {n} -> Set
  refl~~ : {n : ℕ} -> (a : PreSyntax {n}) -> a ~~ a
{-
  o : {n : ℕ} {a aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a :: po aTy
    
  o-== : {n : ℕ} {a a' aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a == a' :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a == po a' :: po aTy
-}

  In : {n : ℕ} -> (Γ : Ctx) -> (v : Fin n)
    -> (ty : PreSyntax {n})  -- use untyped ctx, silly in agda , but makes pencil-paper inducitonscleaner
    -- -> {ty : PreSyntax {n}}
    -- -> Γ |- ty :: pTyU
    -> Set
  
CtxOK : {n : ℕ} -> (Γ : Ctx {n}) -> Set
CtxOK Γ = (v : _) -> (ty : _ ) -> In Γ v ty -> Γ |- ty :: pTyU


data _|-_::_ {n} Γ where
  Var : (v : Fin n) -> {ty : _} -> In Γ v ty -> Γ |- pVar v :: ty
  TyU : Γ |- pTyU :: pTyU
  Cast : {b uty ty : PreSyntax }
    -> Γ |-  b :: uty
    -> Γ |-  uty :: pTyU
    -> Γ |-  ty :: pTyU
    -> Γ |-  pCast b uty ty :: ty
    
  Pi : {aty : PreSyntax } -> {bodty : PreSyntax }
    -> (aTy : Γ |- aty :: pTyU)
    -> (bodTy : Ext Γ aty |- bodty :: pTyU)
    -> Γ |-  pPi aty bodty :: pTyU

  Fun : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> {bod : PreSyntax }
    -- -> (aTy : Γ  |- aty :: pTyU)
    -- -> (bodTy : Ext Γ aty |- bodty :: pTyU)
    -> Ext (Ext Γ aty) (o (pPi aty bodty)) |- bod :: o bodty
    -> Γ |- pFun bod :: pPi aty bodty
    
  App : {f a aty : PreSyntax } -> {bodty : PreSyntax }
    -> Γ |-  f  :: pPi aty bodty -> Γ |- a :: aty 
    -> Γ |-  pApp f a  :: (bodty [ a ])

  Conv : {a m m' : PreSyntax }
    -> Γ |-  a  :: m
    -> m ~~ m'
    -> Γ |-  a  :: m'

postulate
  reg :  {n : ℕ} -> {Γ : Ctx {n}} -> CtxOK Γ -> {a aty : PreSyntax } -> Γ |- a :: aty -> Γ |- aty :: pTyU
