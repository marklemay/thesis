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



_==ctx_ : {n : ℕ} -> (Γ Γ' : Ctx {n}) -> Set -- TODO should be over prectx
Γ ==ctx Γ' = {ty : _} -> {Ty : _}
  -> (v : Fin _)
  -> In {_} {ty} Γ v Ty -> Σ _ \ ty' -> Σ _ \ Ty' ->  Σ (In {_} {ty'} Γ' v Ty') \ _ ->  Γ |- ty == ty' :: pTyU
  










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
    
  ~>pctxr-ext : {n : ℕ} {Γ : Ctx {n}} 
    -> {a a' : _} -> a ~>p a'
    -> {A :  Γ |- a :: pTyU} {A' :  Γ |- a' :: pTyU}
    -> Ext Γ A ~>pctx Ext Γ A'
  ==-trans :  {n : ℕ} {Γ : Ctx {n}} {a a' a'' aty : _}
    -> Γ |- a == a' :: aty ->  Γ |- a' == a'' :: aty
    -> Γ |- a == a'' :: aty
    
  ==-sym :  {n : ℕ} {Γ : Ctx {n}} {a a' aty : _}
    -> Γ |- a == a' :: aty 
    -> Γ |- a' == a :: aty



preservation-ctx== :  {n : ℕ} {Γ Γ' : Ctx {n}} {a aTy : _}
  -> Γ |- a :: aTy -> Γ ~>pctx Γ' 
  -> Γ' |- a :: aTy
preservation-ctx== = {!!}



preservation-ctx~>p :  {n : ℕ} {Γ Γ' : Ctx {n}} {a aTy : _}
  -> Γ |- a :: aTy -> Γ ~>pctx Γ' 
  -> Γ' |- a :: aTy
  
preservation-ctx-==~>p :  {n : ℕ} {Γ Γ' : Ctx {n}} {a a' aTy : _}
  -> Γ |- a == a' :: aTy -> Γ ~>pctx Γ' 
  -> Γ' |- a  == a' :: aTy
preservation-ctx-==~>p (joinV aTy a'Ty a~> a'~>) pctx = joinV (preservation-ctx~>p aTy pctx) (preservation-ctx~>p a'Ty pctx) a~> a'~>

preservation-ctx~>p (Var v {_} {aTY} x) pctx with pctx v x
... | aty' , aTY' , IN , aty~aty' =  Conv (Var v IN) (joinV aTY' (preservation-ctx~>p aTY pctx) par-refl (par-step par-refl aty~aty')) 
preservation-ctx~>p (Pi aty bty) pctx = Pi (preservation-ctx~>p aty pctx) (preservation-ctx~>p bty (~>pctx-ext pctx (par-refll _)))
preservation-ctx~>p (Fun ATy BTy bTy) pctx =
  Fun (preservation-ctx~>p ATy pctx)
    (preservation-ctx~>p BTy (~>pctx-ext pctx (par-refll _)))
    (preservation-ctx~>p bTy (~>pctx-ext (~>pctx-ext pctx (par-refll _)) (par-refll _)))
preservation-ctx~>p (Conv aty x) pctx = Conv (preservation-ctx~>p aty pctx) (preservation-ctx-==~>p x pctx)
preservation-ctx~>p (App aty aty₁) pctx = App (preservation-ctx~>p aty pctx) (preservation-ctx~>p aty₁ pctx)
preservation-ctx~>p (Cast aty aty₁) pctx = Cast (preservation-ctx~>p aty pctx) (preservation-ctx~>p aty₁ pctx)
preservation-ctx~>p TyU pctx = TyU









regularity : {n : ℕ} {Γ : Ctx {n}} {m ty : _}
  -> Γ |- m :: ty
  -> Γ |- ty :: pTyU
  
inv-funTy' : {n : ℕ} {Γ : Ctx {n}} {u aty : _} {bty : _}
  -> Γ |- pPi aty bty :: u ->  Γ |- u == pTyU :: pTyU
  -> Σ (Γ |- aty :: pTyU) \ aTy -> (Ext Γ aTy |- bty :: pTyU)
inv-funTy' (Pi x x₁) eq = x , x₁
inv-funTy' (Conv x eq) eq' = inv-funTy' x (==-trans eq eq')

inv-funTy : {n : ℕ} {Γ : Ctx {n}} {m aty : _} {bty : _}
  -> Γ |- m :: pPi aty bty
  -> Σ (Γ |- aty :: pTyU) \ aTy -> (Ext Γ aTy |- bty :: pTyU)
inv-funTy ty = inv-funTy' (regularity ty) (joinV TyU TyU par-refl par-refl)

regularity (Var v {_} {Ty} x) = Ty
regularity TyU = TyU
regularity (Pi Ty Ty₁) = regularity Ty
regularity (Fun Ty Ty₁ Ty₂) = Pi Ty Ty₁
regularity {_} {Γ} (App {f} {a} {aty} {bodty} fTy aTy) = subst-ty yy aTy
  where
    xxx : Σ (Γ |- aty :: pTyU) (λ z → Ext Γ z |- bodty :: pTyU)
    xxx = inv-funTy fTy
    aTy1 : Γ |- aty :: pTyU
    aTy1 = proj₁ xxx
    yy : Ext Γ aTy1 |- bodty :: pTyU
    yy = proj₂ xxx
regularity (Cast Ty Ty₁) = Ty₁
regularity (Conv Ty (joinV _ x _ _)) = x

 


{-
inv-Pi' :  {n : ℕ} {Γ : Ctx {n}} {aty aty' : _} {b : _} {bty  bty' : _}
  -> Γ |- pFun b :: pPi aty' bty' -> Γ |-  pPi aty' bty'  == pPi aty bty :: pTyU
  -> Σ (Γ |- aty :: pTyU) \ aTy -> Σ (Ext Γ aTy |- bty :: pTyU) \ bTy -> Ext (Ext Γ aTy)  (o (Pi aTy bTy)) |- b :: po bty
inv-Pi' (Fun ty ty₁ ty₂) eq = {!!} , {!!}
inv-Pi' (Conv ty x) eq = {!!} -- inv-Pi' ? (==-trans x eq)




inv-Pi' :  {n : ℕ} {Γ : Ctx {n}} {ty : _} {b : _} 
  -> Γ |- pFun b :: ty
  -> Σ _ \ aty -> Σ _ \ bty
  -> Σ (Γ |- aty :: pTyU) \ aTy -> Σ (Ext Γ aTy |- bty :: pTyU) \ bTy
  -> Σ (Γ |- ty == (pPi aty bty) :: pTyU) \ _
  -> Ext (Ext Γ aTy) (o (Pi aTy bTy)) |- b :: po bty
inv-Pi' = {!!}


inv-Pi :  {n : ℕ} {Γ : Ctx {n}} {a aty pity : _} {b : _} {bty : _}
  -> Γ |- pFun b :: pity -> Γ |- pity == pPi aty bty :: pTyU
  -> Σ (Γ |- aty :: pTyU) \ aTy -> Σ (Ext Γ aTy |- bty :: pTyU) \ bTy -> Ext (Ext Γ aTy)  (o (Pi aTy bTy)) |- b :: po bty
inv-Pi (Fun ty ty₁ ty₂) eq = {!!}
inv-Pi (Conv ty x) eq = {!!}
-}

{-
inv-Pi'' :  {n : ℕ} {Γ : Ctx {n}} {aty ty : _} {b : _} {bty  : _}
  -> Γ |- pFun b :: ty
  -> Γ |-  ty == pPi aty bty :: pTyU -> (aTy : Γ |- aty :: pTyU) -> (bTy : Ext Γ aTy |- bty :: pTyU)
  -> Ext (Ext Γ aTy)  (o (Pi aTy bTy)) |- b :: po bty
inv-Pi'' (Fun ty ty₁ ty₂) (joinV x piTy x₂ x₃) = {!!}
  where
    
    xx = inv-funTy' piTy (joinV TyU TyU par-refl par-refl)
    
    
inv-Pi'' (Conv ty x) eq = {!!}
-}




inv-Pi'' :  {n : ℕ} {Γ : Ctx {n}} {aty ty : _} {b : _} {bty  : _}
  -> Γ |- pFun b :: ty
  -> Γ |-  ty == pPi aty bty :: pTyU -> (aTy : Γ |- aty :: pTyU) -> (bTy : Ext Γ aTy |- bty :: pTyU)
  -> Ext (Ext Γ aTy)  (o (Pi aTy bTy)) |- b :: po bty
inv-Pi'' (Fun ty ty₁ ty₂) e = {!!}
  where
    
    
inv-Pi'' (Conv ty x) eq = {!!}



preservation~>p :  {n : ℕ} {Γ : Ctx {n}} {a a' aTy : _}
  -> Γ |- a :: aTy  -> a ~>p a'
  -> Γ |- a' :: aTy



preservation~>p (Pi ATy BTy) (par-Pi aty~> bty~>) =
  Pi (preservation~>p ATy aty~>) (preservation~>p (preservation-ctx~>p BTy (~>pctxr-ext aty~>)) bty~>)
preservation~>p (Fun ATy BTy bTy) (par-Fun b~>) =
  Fun ATy BTy (preservation~>p bTy b~>)
preservation~>p  {_} {Γ} (App {_} {a} {aty} {bty} fTy aTy) (par-red {_} {a'} {b} {b'} a~> b~>) = {!!}
  where
    f'Ty : Γ |- pFun b' :: pPi aty bty
    f'Ty = preservation~>p fTy (par-Fun b~>)
    
    a'Ty : Γ |- a' :: aty
    a'Ty = preservation~>p aTy a~>
    
    -- inversion,  Γ, aty ,  pPi aty bty |- b' :: bty
    -- subst, Γ, |- b'[a',f'] :: bty[a'] (f unbound in bty)
    -- subst-conv, Γ, |- b'[a',f'] :: bty[a]
preservation~>p  {_} {Γ} (App {_} {a} {aty} {bty} fTy aTy) (par-App {f} {f'} {a} {a'} f~> a~>)= final
  where
    a'Ty : Γ |- a' :: aty
    a'Ty = preservation~>p aTy a~>
    
    f'a'Ty : Γ |- pApp f' a' :: (bty [ a' ])
    f'a'Ty = App (preservation~>p fTy f~>) a'Ty

    ATyTY : Γ |- aty :: pTyU
    ATyTY = proj₁ (inv-funTy fTy)
    Fwf : (Ext Γ ATyTY) |- bty :: pTyU
    Fwf = proj₂ (inv-funTy fTy)
    
    final : Γ |- pApp f' a' :: (bty [ a ])
    final = Conv f'a'Ty (joinV (subst-ty Fwf a'Ty) (subst-ty Fwf aTy) par-refl (par-step par-refl (sub-par (par-refll bty) a~>)))

preservation~>p (Cast aTy ATy) (par-cast-red par) = preservation~>p aTy par
preservation~>p {_} {Γ} {pAnn a A} (Cast aty Aty) (par-cast {_} {a'} {_} {A'} a-a' A-A') = final
  where 
    a'ty : Γ |- a' :: A
    a'ty = preservation~>p aty a-a'
    
    A'ty : Γ |- A' :: pTyU
    A'ty = preservation~>p Aty  A-A'

    a'ty' : Γ |- a' :: A'
    a'ty' = Conv a'ty (joinV Aty A'ty (par-step par-refl A-A') par-refl) 
    
    almost : Γ |- pAnn a' A' :: A'
    almost = Cast a'ty' A'ty
    final : Γ |- pAnn a' A' :: A
    final = Conv almost (joinV A'ty Aty par-refl (par-step par-refl A-A'))
  
preservation~>p (Conv Ty x) par = Conv (preservation~>p Ty par) x
preservation~>p (Var v x) par-Var = Var v x
preservation~>p TyU par-TyU = TyU

{-
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
-}
