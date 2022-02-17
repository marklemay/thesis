module reg where

import presyntax as p

--import syn as r
import syn-paper as w

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding ([_])



data _|-_::_ {n : ℕ} (Γ : p.pCtx {n}) : p.PreSyntax {n}  ->  p.PreSyntax {n} -> Set


CtxOK : {n : ℕ} -> (Γ : p.pCtx {n}) -> Set
CtxOK Γ = (v : _) -> (ty : _ ) -> p.In Γ v ty -> Γ |- ty :: p.pTyU



data  _|-_==_::_ {n : ℕ} (Γ : p.pCtx {n}) :  p.PreSyntax {n} ->  p.PreSyntax {n} ->  p.PreSyntax {n} -> Set  where
  joinV : {n m m' ty : _}
    -> Γ |- m :: ty
    -> Γ |- m' :: ty
    -> m p.~>p* n
    -> m' p.~>p* n
    -> Γ |- m == m' :: ty

postulate
  o : {n : ℕ} {Γ : p.pCtx} -> {a aTy ty : p.PreSyntax {n}}
    -> p.pExt Γ ty |- p.po a :: p.po aTy
    {-
  o-== : {n : ℕ} {a a' aTy ty : p.PreSyntax {n}} {Γ : p.pCtx} -> Γ |- a == a' :: aTy -> {Ty : Γ |- ty :: p.pTyU}
    -> p.pExt Γ Ty |- p.po a == p.po a' :: p.po aTy -}


-- redo the rules here since the regular version has slightly different ctxs
data _|-_::_ {n} Γ  where
  Var : (v : Fin n) -> {ty : _} -> p.In Γ v ty
    -> {CtxOK Γ}
    -> Γ |- p.pVar v :: ty
  
  TyU : {CtxOK Γ}
    -> Γ |- p.pTyU :: p.pTyU
  
  Pi : { aty : p.PreSyntax } -> {bodty : p.PreSyntax }
    -> (aTy : Γ  |- aty :: p.pTyU)
    -> (bodTy : p.pExt Γ aty |- bodty :: p.pTyU)
    -> Γ |-  p.pPi aty bodty :: p.pTyU
    
  Fun : { aty : p.PreSyntax } -> {bodty : p.PreSyntax }
    -> {bod : p.PreSyntax }
    -> (aTy : Γ  |- aty :: p.pTyU)
    -> (bodTy : p.pExt Γ aty |- bodty :: p.pTyU)
    -> p.pExt (p.pExt Γ aty)  (p.po (p.pPi aty bodty)) |- bod :: p.po bodty
    -> Γ |- p.pFun bod :: p.pPi aty bodty
    
  App : {f a aTy : p.PreSyntax } -> {bodTy : p.PreSyntax }
    -> Γ |- f  :: p.pPi aTy bodTy -> Γ  |- a :: aTy 
    -> Γ |- p.pApp f a  :: (bodTy p.[ a ])
    
  Ann : {e : p.PreSyntax } -> {ty : p.PreSyntax }
    -> Γ |-  e :: ty
    -- -> Γ |-  ty :: p.pTyU
    -> Γ |-  p.pAnn e ty  :: ty
    
  Conv : {a m m' : p.PreSyntax }
    -> Γ |-  a :: m
    -> Γ |- m == m' :: p.pTyU
    -> Γ |- a :: m'


-- some sanity check lemmas

toweak : {n : ℕ} -> (Γ : p.pCtx {n}) -> {a aty : _ } -> Γ |- a :: aty -> Γ w.|- a :: aty
toweak Γ (Var v x) = w.Var v x
toweak Γ TyU = w.TyU
toweak Γ (Pi x x₁) = w.Pi (toweak Γ x) (toweak (p.pExt Γ _) x₁)
toweak Γ (Fun x x₁ x₂) = w.Fun (toweak _ x₂)
toweak Γ (App x x₁) = w.App (toweak Γ x) (toweak Γ x₁)
toweak Γ (Ann x) = w.Ann (toweak Γ x)
toweak Γ (Conv x (joinV x₁ x₂ x₃ x₄)) = w.Conv (toweak Γ x) (w.joinV x₃ x₄)


ctxok :  {n : ℕ} -> (Γ : p.pCtx {n}) -> {a aty : _ } -> Γ |- a :: aty -> CtxOK Γ
ctxok Γ (Var v x {ok}) = ok
ctxok Γ (TyU {ok}) = ok
ctxok Γ (Pi x x₁) = ctxok Γ x
ctxok Γ (Fun x x₁ x₂) = ctxok Γ x
ctxok Γ (App x x₁) = ctxok Γ x
ctxok Γ (Ann x) = ctxok Γ x
ctxok Γ (Conv x x₁) = ctxok Γ x

isReg : {n : ℕ} -> (Γ : p.pCtx {n}) -> {a aty : _ } -> Γ |- a :: aty -> Γ |- aty :: p.pTyU
isReg Γ (Var v  x {ok}) = ok v _ x
isReg Γ (TyU {ok}) = TyU {_} {_} {ok}
isReg Γ (Pi x x₁) = TyU {_} {_} {ctxok Γ x} -- also by (isReg Γ x) 
isReg Γ (Fun x x₁ x₂) = Pi x x₁
isReg Γ (App f a) = {!!} -- by induction on  (Γ |- p.pPi aTy bodTy) and inversion/ or to weak (bodTy : ty) by sub  (bodTy[a] : ty) -- most these steps can be inderected through toweak
isReg Γ (Ann x) = isReg Γ x
isReg Γ (Conv x (joinV x₁ x₂ x₃ x₄)) = x₂

tyReg :  {n : ℕ} -> (Γ : p.pCtx {n}) -> CtxOK Γ -> {a aty : _ } -> Γ w.|- aty :: p.pTyU -> Γ |- aty :: p.pTyU
tyReg Γ ok x = {!!}
-- agda case split is too dumb



almostreg : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> (ty : Γ w.|- a :: aty) -> Σ _ λ aty' →  Σ (aty w.~~ aty') λ _ →  Γ w.|- aty' :: p.pTyU
almostreg = {!!}

regty :  {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a : _ } -> Γ w.|- a :: p.pTyU -> Γ |- a :: p.pTyU
regty = {!!}


toreg'' : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> Γ w.|- a :: aty -> Γ |- aty :: p.pTyU -> Γ |- a :: aty
toreg'' = {!!} 

toreg' : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> Γ w.|- a :: aty -> {aty' : _ } -> aty w.~~ aty' -> Γ |- aty' :: p.pTyU -> Γ |- a :: aty'
toreg' ok (w.Var v x) eq ATy = {!!}
toreg' ok w.TyU  eq ATy = {!!}
toreg' ok (w.Pi A A₁) eq ATy = {!!}
toreg' ok (w.Fun A) eq ATy = {!!}
toreg' {_} {Γ} ok (w.App {f} {aty} {bodty} fTy {a} aTy) {outTy} eq ATy  = Conv (App fPi  x1') x3
  where
    x1 : Γ w.|- aty :: p.pTyU
    x1 = {!!}
    
    x1' : Γ |- a :: aty
    x1' = toreg'' ok aTy (regty ok x1)
    
    x2 :  p.pExt Γ aty w.|- bodty :: p.pTyU
    x2 = {!!}
    
    x2' :  p.pExt Γ aty |- bodty :: p.pTyU
    x2' = regty {!!} x2

    fPi : Γ |- f :: p.pPi aty bodty
    fPi = toreg'' ok fTy (Pi (regty ok x1) x2')

    left : Γ |- bodty p.[ a ] :: p.pTyU
    left = regty ok {!!} -- ty sub

    x3 : Γ |- (bodty p.[ a ]) == outTy :: p.pTyU
    x3 = {!!} 

toreg' ok (w.Ann A) eq ATy  = {!!}
toreg' ok (w.Conv A x) eq ATy  = toreg' ok A {!!} ATy  -- by weakening == and transitivity

toreg : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> Γ w.|- a :: aty -> Γ  w.|- aty :: p.pTyU -> Γ |- a :: aty
toreg = {!!}


{-
fromConv : {n : ℕ} -> {Γ : p.pCtx {n}} -> {a aty : _ } -> Γ w.|- a :: aty -> Bool
fromConv (w.Var v x) = false
fromConv w.TyU = false
fromConv (w.Pi x x₁) = false
fromConv (w.Fun x) = false
fromConv (w.App x x₁) = false
fromConv (w.Ann x) = false
fromConv (w.Conv x x₁) = true


full : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> (ty : Γ w.|- a :: aty) -> {!!}
full = {!!}

direct : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> (ty : Γ w.|- a :: aty) -> fromConv ty ≡ false ->  Γ  w.|- aty :: p.pTyU
direct = {!!}



indirect : {n : ℕ} -> {Γ : p.pCtx {n}} -> CtxOK Γ -> {a aty : _ } -> (ty : Γ w.|- a :: aty) -> fromConv ty ≡ true -> Σ {!!} {!!}
indirect = {!!}



postulate
  Eq : {n : ℕ} -> {Γ : p.pCtx {n}} -> {aty : _ } -> Γ |- aty :: p.pTyU -> {aty' : _ } -> Γ |- aty' :: p.pTyU -> aty w.~~ aty' -> Γ |- aty == aty' :: p.pTyU


toregty : {n : ℕ} -> (Γ : p.pCtx {n}) -> CtxOK Γ -> {a  : _ } -> Γ w.|- a :: p.pTyU -> Γ |- a :: p.pTyU

toreg : {n : ℕ} -> (Γ : p.pCtx {n}) -> CtxOK Γ -> {a aty : _ } -> Γ w.|- a :: aty -> Γ w.|- aty :: p.pTyU -> Γ |- a :: aty

-- CtxOK Γ is implied by  Γ |- aty' :: p.pTyU 
toreg' : {n : ℕ} -> (Γ : p.pCtx {n}) -> CtxOK Γ -> {a aty : _ } -> Γ w.|- a :: aty -> {aty' : _ } -> aty w.~~ aty' -> Γ |- aty' :: p.pTyU -> Γ |- a :: aty'
toreg' Γ ok (w.Var v x) eq atyty = Conv (Var v x {ok}) (Eq (ok v _ x) atyty eq)
toreg' Γ ok w.TyU eq atyty = Conv (TyU {_} {_} {ok}) (Eq (TyU {_} {_} {ok}) atyty eq)
toreg' Γ ok (w.Pi aty bty) eq atyty = Conv (Pi (toregty Γ ok aty) (toregty (p.pExt Γ _) {!!} bty)) (Eq (TyU {_} {_} {ok}) atyty eq) -- CtxOK by aty
toreg' Γ ok (w.Fun bty) eq atyty = Conv (Fun {!!} {!!} (toreg' {!!} {!!} bty {!!} {!!})) {!!}
  -- pretty sure this is ok, just a lot of bookkeeping
    
toreg' Γ ok (w.App {f} {aty} {bodty} fTy {a} aTy) eq atyty = Conv (App fTy' aTy') {!!}
  where
    
    fTy' : Γ |- f :: p.pPi aty bodty
    fTy' = toreg Γ ok fTy {!!}

    aTy' : Γ |- a :: aty
    aTy' = toreg Γ ok aTy {!!}
    
toreg' Γ ok (w.Ann aty) eq atyty = {!!}
toreg' Γ ok {a} {aty} (w.Conv aTy ee) {aty'} eq aTyty = toreg' Γ ok aTy {!!} aTyty -- by weakening == and transitivity

toregty Γ ok x = toreg' Γ ok x (w.joinV p.par-refl p.par-refl) (TyU {_} {_} {ok})
toreg Γ ok x xty = toreg' Γ ok x (w.joinV p.par-refl p.par-refl) (toreg' Γ ok xty (w.joinV p.par-refl p.par-refl) (TyU {_} {_} {ok}))

 -- where
 --   leap : Γ |- a :: aty'
 --   leap = toreg' Γ ok aTy {!!} aTyty -- by weakening == and transitivity


toreg : {n : ℕ} -> (Γ : p.pCtx {n}) -> CtxOK Γ -> {a aty : _ } -> Γ w.|- a :: aty -> Γ w.|- aty :: p.pTyU -> Γ |- a :: aty
toreg Γ ok (w.Var v x) _ = Var v _ x {ok}
toreg Γ ok w.TyU _ = TyU {_} {_} {ok} 
toreg Γ ok (w.Pi aty aty₁) _ = Pi (toreg Γ ok aty w.TyU) (toreg (p.pExt Γ _) {!!} aty₁ w.TyU) -- context ok invarient is met by aty
toreg Γ ok (w.Fun aty) atyty = Fun {!!} {!!} {!!}
toreg Γ ok (w.App aty aty₁) atyty = App {!!} {!!}
toreg Γ ok (w.Ann aty) atyty = Ann (toreg Γ ok aty atyty)
toreg Γ ok (w.Conv aty (w.joinV x x₁)) atyty = Conv {!!} {!!} -- this proof attempt doesn't work beuase you can CONV in and out of dumb untyped types


conv : {n : ℕ} -> {Γ : p.pCtx {n}} -> {CtxOK Γ} -> {a aty : _ } -> Γ |- a :: aty -> {aty' : _ } -> aty w.~~ aty' -> Γ |- aty' :: p.pTyU -> Γ |- a :: aty'
conv Γ x x₁ x₂ x₃ = Conv {!!} {!!}

-}
