

module syn where

import presyntax as p

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
data _|-_::_ {n : ℕ} (Γ : Ctx {n}) : p.PreSyntax {n}  ->  p.PreSyntax {n} -> Set

-- definitional eq
data  _==_ {n : ℕ} :  p.PreSyntax {n} ->  p.PreSyntax {n} -> Set  where
  joinV : {n m m' : _}
    -> m p.~>p* n
    -> m' p.~>p* n
    -> m == m'

data Ctx where
  Emp : Ctx {zero}
  Ext : {n : ℕ} -> (Γ : Ctx) -> p.PreSyntax {n} -> Ctx {suc n}

postulate
  o : {n : ℕ} {a aTy ty : p.PreSyntax {n}} {Γ : Ctx} -> Γ |- a :: aTy 
    -> Ext Γ aTy |- p.po a :: p.po aTy
    
--  o-== : {n : ℕ} {a a' aTy ty : p.PreSyntax {n}} ->  a == a' 
--    -> Ext Γ aTy |- p.po a == p.po a' 
  In : {n : ℕ} {ty : p.PreSyntax {n}} -> (Γ : Ctx) -> (v : Fin n) -> Γ |- ty :: p.pTyU -> Set 


data _|-_::_ {n} Γ  where
  Var : (v : Fin n) -> {ty : _} -> {Ty : _} -> In {_} {ty} Γ v Ty -> Γ |- p.pVar v :: ty
  TyU : Γ |- p.pTyU :: p.pTyU
  Pi : { aty : p.PreSyntax } -> {bodty : p.PreSyntax }
    -> (aTy : Γ  |- aty :: p.pTyU)
    -> (bodTy : Ext Γ aty |- bodty :: p.pTyU)
    -> Γ |-  p.pPi aty bodty :: p.pTyU
    
  Fun : { aty : p.PreSyntax } -> {bodty : p.PreSyntax }
    -> {bod : p.PreSyntax }
    -> (aTy : Γ  |- aty :: p.pTyU)
    -> (bodTy : Ext Γ aty |- bodty :: p.pTyU)
    -> Ext (Ext Γ aty)  (p.po (p.pPi aty bodty)) |- bod :: p.po bodty
    -> Γ |- p.pFun bod :: p.pPi aty bodty
    
  App : {f a aTy : p.PreSyntax } -> {bodTy : p.PreSyntax }
    -> Γ |-  f  :: p.pPi aTy bodTy -> Γ  |- a :: aTy 
    -> Γ |-  p.pApp f a  :: (bodTy p.[ a ])
  Ann : {e : p.PreSyntax } -> {ty : p.PreSyntax }
    -> Γ |-  e :: ty
    -> Γ |-  ty :: p.pTyU
    -> Γ |-  p.pAnn e ty  :: ty
    
  Conv : {a m m' : p.PreSyntax}
    -> Γ |-  a  :: m
    -> m == m'
    -> Γ |-  a  :: m'


--postulate
--  ok :  {n : ℕ} {Γ : PreCtx n} {a aTy : _} -> Γ |- a :: aTy -> Ctx {_} {Γ}
--  lookup :  {n : ℕ} {Γ : PreCtx n} -> (Ctx  {_} {Γ}) -> Fin n -> Σ _ \ aTy -> Γ |- aTy :: pTyU

