module sketch where

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import presyntax



{-
stable-tyu :  {n : ℕ} {Γ : Ctx n}  {a  ty : _}
   -> Γ |- pTyU ~>*p a :: ty
   -> a ≡ pTyU
stable-tyu (par-refl x) = refl
stable-tyu (par-step rest step) with stable-tyu rest
stable-tyu (par-step rest par-TyU) | refl = refl


stable-pi :  {n : ℕ} {Γ : Ctx n}  {a aTy ty : _} {bodTy : _}
   -> Γ |- pPi aTy bodTy ~>*p a :: ty
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  -> a ≡ pPi aTy' bodTy' 
stable-pi {n} {Γ}  {a} {aTy} {ty} {bodTy} (par-refl x) = aTy , bodTy , refl
stable-pi (par-step front step) with stable-pi front
stable-pi (par-step front (par-Pi step step₁)) | fst , xx = _ , _ , refl
-}


postulate
  Tel : ℕ -> ℕ -> Set
  +++ : {n m : ℕ} (Γ : Ctx n) -> Tel n m -> Ctx (n + m)
--  _[_]tel : Tel n m
  
subst-ty : {!!} 
subst-ty = {!!}

-- needed to work around conv
--pi-ty-inv :{n : ℕ} {Γ : Ctx n} {b ATy : _} {BTy : _}
--  -> Γ |- pFun b :: e -> e === pPi ATy BTy
--  -> Γ ,, a ,, f |- b :: o BTy

_~>pctx_ : {n : ℕ} -> (Γ : Ctx n) -> (Γ' : Ctx n) -> Set -- TODO should be over prectx
Γ ~>pctx Γ' = (v : Fin _) -> lookup Γ v  ~>p  lookup Γ' v



preservation~>p :  {n : ℕ} {Γ : Ctx n} {a a' aTy : _}
  -> Γ |- a :: aTy -> a ~>p a'
  -> Γ |- a' :: aTy

-- TODO could rap this up in single recursion?
ctxstep-== : {n : ℕ} {Γ Γ' : Ctx n} {a a' aTy : _}
  -> Γ ~>pctx Γ' -> Γ |- a == a' :: aTy
  -> Γ' |- a == a' :: aTy
  
ctxstep-ty : {n : ℕ} {Γ Γ' : Ctx n} {a aTy : _}
  -> Γ ~>pctx Γ' -> Γ |- a :: aTy ->  Γ' |- a :: aTy
ctxstep-ty {_} {Γ} {Γ'} Γ-Γ' (Var v) = Conv (Var v) (joinV {!!} ? par-refl (par-step par-refl (Γ-Γ' v))) -- TODO need the ctx ok, so needs to be mutial with SR
  where
    lk : lookup Γ v ~>p lookup Γ' v
    lk = Γ-Γ' v
ctxstep-ty Γ-Γ' (Pi ty ty₁) = {!!}
ctxstep-ty Γ-Γ' (Fun ty ty₁ ty₂) = {!!}
ctxstep-ty Γ-Γ' (Conv ty eq) = Conv (ctxstep-ty  Γ-Γ' ty) (ctxstep-== Γ-Γ' eq)
ctxstep-ty Γ-Γ' (App ty ty₁) = App (ctxstep-ty Γ-Γ' ty) (ctxstep-ty Γ-Γ' ty₁)
ctxstep-ty Γ-Γ' (Cast ty ty₁) = Cast (ctxstep-ty Γ-Γ' ty) (ctxstep-ty Γ-Γ' ty₁)
ctxstep-ty Γ-Γ' TyU = TyU

ctxstep-== Γ-Γ' (joinV aTy a'Ty a-b a'-b) = joinV (ctxstep-ty Γ-Γ' aTy) (ctxstep-ty Γ-Γ' a'Ty) a-b a'-b


preservation~>p (Var v) par-Var = Var v
preservation~>p TyU par-TyU = TyU
preservation~>p  {_} {Γ} {pPi a b} {pPi a' b'} (Pi aty bty) (par-Pi a-a' b-b') = {!!}
  where
    a'ty : Γ |- a' :: pTyU
    a'ty = preservation~>p aty a-a'

    b'ty : extCtx Γ a |- b' :: pTyU
    b'ty = preservation~>p bty b-b'
    
    -- pPi a b' :: pTyU   which isn't particularly helpful
    -- need to allow typed step in ctx


preservation~>p (Fun Aty Bty bty) (par-Fun red) = Fun Aty Bty (preservation~>p bty red)
preservation~>p {_} {Γ} {pApp (pFun b) a}
  (App {_} {_} {ATy} {BTy} fty aty) (par-red {_} {a'} {_} {b'} a-a' b-b') = {!!}
  where
    a'ty : Γ |- a' :: ATy
    a'ty = preservation~>p aty a-a'
    
    b'ty :  {! Γ ,, f ,, ATy!} |- b' :: o BTy 
    b'ty = preservation~>p {!!} b-b' -- from inversion
    
    fun'ty : Γ |- pFun b' :: pPi ATy BTy 
    fun'ty = preservation~>p fty (par-Fun b-b')
  -- Γ |- (b' [ o (pFun b') ]) [ a' ] :: (BTy [ a ])
  --                                              by subst step-ty (or conversion), suffices to show
  -- Γ |- (b' [ o (pFun b') ]) [ a' ] :: (BTy [ a' ])
  -- Γ |- (b' [ o (pFun b') ]) [ a' ] :: (BTy [ a' ]) which follows by typed subst
  
preservation~>p {_} {Γ} {pApp f a} {pApp f' a'}
  (App {_} {_} {aTy} {bodTy} fty aty) (par-App f-f' a-a') = {!!}
  where
    a'ty : Γ |- a' :: aTy
    a'ty = preservation~>p aty a-a'
    f'ty : Γ |- f' :: pPi aTy bodTy
    f'ty = preservation~>p fty f-f'
  -- Γ |- f' a' :: (bodTy [ a  ])
  --                                              by subst step-ty (or conversion), suffices to show
  -- Γ |- f' a' :: (bodTy [ a' ]) by ty
preservation~>p {_} {Γ} {pAnn a A} (Cast aty Aty) (par-cast-red red) = preservation~>p aty red
preservation~>p {_} {Γ} {pAnn a A} (Cast aty Aty) (par-cast {_} {a'} {_} {A'} a-a' A-A') = final
  where
    a'ty : Γ |- a' :: A
    a'ty = preservation~>p aty a-a'
    a'ty' : Γ |- a' :: A'
    A'ty : Γ |- A' :: pTyU
    A'ty = preservation~>p Aty A-A'
    a'ty' = Conv a'ty (joinV Aty A'ty (par-step par-refl A-A') par-refl) -- (joinV (par-step (par-refl Aty) A-A') (par-refl A'ty))
    almost : Γ |- pAnn a' A' :: A'
    almost = Cast a'ty' A'ty
    final : Γ |- pAnn a' A' :: A
    final = Conv almost (joinV A'ty Aty par-refl (par-step par-refl A-A')) -- (joinV (par-refl A'ty) (par-step (par-refl Aty) A-A'))
preservation~>p (Conv ty x) red = Conv (preservation~>p ty red) x



{-

-- progress

data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU : pTyU val
  vPi : { aTy : PreSyntax } -> {bodTy : PreSyntax }
     -> (pPi aTy bodTy) val
  vFun : {bod : PreSyntax {suc (suc n)} }
    -> (pFun bod) val
  -- TODO should casts be values?

data  _~>_ {n : ℕ} : PreSyntax {n} ->  PreSyntax {n} -> Set where
  app-red : {a  : PreSyntax} ->  {bod : PreSyntax {suc (suc n)} }
    ->  a val
    -> (pApp (pFun bod)  a) ~> ( bod [ o (pFun  bod) ] [ a ]  )
    
  cast-red : {e : PreSyntax} -> {ty : PreSyntax}
    ->  e val
    -> (pAnn e ty) ~> e
    
  -- structural
  appf-struc : {f f' a : PreSyntax } -> f ~> f' -> pApp f a ~> pApp f' a
  appa-struc : {f a a' : PreSyntax } -> f val -> a ~> a' -> pApp f a ~> pApp f a'
  
  cast-struc : {e e' : PreSyntax} -> {ty : PreSyntax}
    ->  e ~> e' 
    -> (pAnn e ty) ~> (pAnn e' ty) 
-}
