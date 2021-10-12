module pres where

open import presyntax
open import syn


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
stable-tyu :  {n : ℕ} {Γ : PreCtx n}  {a  ty : _}
   -> Γ |- pTyU ~>*p a :: ty
   -> a ≡ pTyU
stable-tyu (par-refl x) = refl
stable-tyu (par-step rest step) with stable-tyu rest
stable-tyu (par-step rest par-TyU) | refl = refl


stable-pi :  {n : ℕ} {Γ : PreCtx n}  {a aTy ty : _} {bodTy : _}
   -> Γ |- pPi aTy bodTy ~>*p a :: ty
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  -> a ≡ pPi aTy' bodTy' 
stable-pi {n} {Γ}  {a} {aTy} {ty} {bodTy} (par-refl x) = aTy , bodTy , refl
stable-pi (par-step front step) with stable-pi front
stable-pi (par-step front (par-Pi step step₁)) | fst , xx = _ , _ , refl
-}

  
subst-ty : {n : ℕ} {Γ : Ctx {n}} {b bty : _}  {aty : _} {ATy : Γ |- aty :: pTyU}
  -> Ext Γ ATy |- b :: bty
  -> {a : _} -> Γ |- a :: aty
  -> Γ |- (b [ a ]) :: (bty [ a ])
subst-ty = {!!}


_~>pctx_ : {n : ℕ} -> (Γ Γ' : Ctx {n}) -> Set -- TODO should be over prectx
Γ ~>pctx Γ' = {ty : _} ->  {Ty : _}
  -> (v : Fin _)
  -> In {_} {ty} Γ v Ty -> Σ _ \ ty' -> Σ _ \ Ty' ->  Σ (In {_} {ty'} Γ' v Ty') \ _ ->  ty ~>p ty'

postulate
  ~>pctx-ext : {n : ℕ} {Γ Γ' : Ctx {n}} 
    -> Γ ~>pctx Γ'
    -> {a a' : _} -> a ~>p a'
    -> {A :  Γ |- a :: pTyU} {A' :  Γ' |- a' :: pTyU}
    -> Ext Γ A ~>pctx Ext Γ' A'

inv-Pi' :  {n : ℕ} {Γ : Ctx {n}} {ty : _} {b : _} 
  -> Γ |- pFun b :: ty
  -> Σ _ \ aty -> Σ _ \ bty
  -> Σ (Γ |- aty :: pTyU) \ aTy -> Σ (Ext Γ aTy |- bty :: pTyU) \ bTy
  -> Σ (Γ |- ty == (pPi aty bty) :: pTyU) \ _
  -> Ext (Ext Γ aTy) (o (Pi aTy bTy)) |- b :: po bty
inv-Pi' = {!!}

inv-Pi :  {n : ℕ} {Γ : Ctx {n}} {a aty : _} {b : _} {bty : _}
  -> Γ |- pFun b :: pPi aty bty
  -> Σ (Γ |- aty :: pTyU) \ aTy -> Σ (Ext Γ aTy |- bty :: pTyU) \ bTy -> Ext (Ext Γ aTy)  (o (Pi aTy bTy)) |- b :: po bty
inv-Pi = {!!}

preservation~>p :  {n : ℕ} {Γ Γ' : Ctx {n}} {a a' aTy : _}
  -> Γ |- a :: aTy -> Γ ~>pctx Γ' -> a ~>p a'
  -> Γ' |- a' :: aTy

preservation-==~>p :  {n : ℕ} {Γ Γ' : Ctx {n}} {a a' aTy : _}
  -> Γ |- a == a' :: aTy -> Γ ~>pctx Γ'
  -> Γ' |- a == a' :: aTy
preservation-==~>p (joinV aTy a'Ty a~> a'~>) pctx = joinV (preservation~>p aTy pctx (par-refll _)) (preservation~>p a'Ty pctx (par-refll _)) a~> a'~>

preservation~>p (Pi ATy BTy) pctx (par-Pi A~> B~>) =
  Pi (preservation~>p ATy pctx A~>) (preservation~>p BTy (~>pctx-ext pctx A~>) B~>) --need to reange over ctx jusf for this
preservation~>p (Fun ATy BTy bTy) pctx (par-Fun pa) =
  Fun (preservation~>p ATy pctx (par-refll _))
    (preservation~>p BTy (~>pctx-ext pctx (par-refll _)) (par-refll _))
    (preservation~>p bTy (~>pctx-ext (~>pctx-ext pctx (par-refll _)) (par-refll _)) pa)
preservation~>p {_} {Γ} {Γ'} (App {_} {a} {aty} {bty} fTy aTy) pctx (par-red {_} {a'} {b} {b'} a~> b~>) = {!!}
  where
    a'ty : Γ' |- a' :: aty 
    a'ty = preservation~>p aTy pctx a~>

    aTyTy : Γ |- aty :: pTyU
    aTyTy = proj₁ (inv-Pi fTy)
    xxx : Ext Γ aTyTy |- bty :: pTyU
    xxx = proj₁ (proj₂ (inv-Pi fTy))
    yyy : Ext (Ext Γ aTyTy) (o (Pi aTyTy xxx)) |- b :: po bty
    yyy = proj₂  (proj₂ (inv-Pi fTy))
    
    aTyTy' : Γ' |- aty :: pTyU 
    aTyTy' = preservation~>p aTyTy pctx (par-refll _)

    BTy : Ext Γ' aTyTy' |- bty :: pTyU
    BTy = preservation~>p xxx (~>pctx-ext pctx (par-refll _)) (par-refll _)
    
    zzz : Ext (Ext Γ' aTyTy') (o (Pi aTyTy' BTy)) |- b' :: po bty
    zzz = preservation~>p yyy (~>pctx-ext (~>pctx-ext pctx (par-refll _)) (par-refll _)) b~>

    -- subst-ty Γ' |- (b' [ o (pFun b') ]) [ a' ] :: (bodTy [ a' ])
    -- conv-sbst  Γ' |- (b' [ o (pFun b') ]) [ a' ] :: (bodTy [ a ])
preservation~>p {_} {Γ} {Γ'} (App {_} {a} {aty} {bty} fTy aTy) pctx  (par-App {f} {f'} {a} {a'} f~> a~>) = conv-subst
  where
    a'Ty : Γ' |- a' :: aty 
    a'Ty = preservation~>p aTy pctx a~>
    
    f'Ty : Γ' |- f' :: pPi aty bty
    f'Ty = preservation~>p fTy pctx f~>
    f'a' : Γ' |- pApp f' a' :: (bty [ a' ])
    f'a' = App f'Ty a'Ty
    conv-subst : Γ' |- pApp f' a' :: (bty [ a ])
    conv-subst = {!!}
    
preservation~>p {_} {Γ} {Γ'} {pAnn a A} (Cast aty Aty) pctx (par-cast {_} {a'} {_} {A'} a-a' A-A') = final
  where 
    a'ty : Γ' |- a' :: A
    a'ty = preservation~>p aty pctx a-a'
    
    A'ty : Γ' |- A' :: pTyU
    A'ty = preservation~>p Aty pctx  A-A'

    ATy' : Γ' |- A :: pTyU
    ATy' = preservation~>p Aty pctx (par-refll _)
    a'ty' = Conv a'ty (joinV ATy' A'ty (par-step par-refl A-A') par-refl) 
    
    almost : Γ' |- pAnn a' A' :: A'
    almost = Cast a'ty' A'ty
    final : Γ' |- pAnn a' A' :: A
    final = Conv almost (joinV A'ty ATy' par-refl (par-step par-refl A-A'))
  
preservation~>p {_} {Γ} {Γ'} {pAnn a A} (Cast aty Aty) pctx (par-cast-red aa) = preservation~>p aty pctx aa
preservation~>p (Conv ty eq) pctx a = Conv (preservation~>p ty pctx a) (preservation-==~>p eq pctx)
preservation~>p (Var v {_} {aTY} x) pctx par-Var with pctx v x
... | aty' , aTY' , IN , aty~aty' = Conv (Var v IN) (joinV aTY' (preservation~>p aTY pctx (par-refll _)) par-refl (par-step par-refl aty~aty'))
preservation~>p TyU pctx par-TyU = TyU
