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



_==ctx_ : {n : ℕ} -> (Γ Γ' : Ctx {n}) -> Set
Γ ==ctx Γ' = {ty : _} -> {Ty : _}
  -> (v : Fin _)
  -> In {_} {ty} Γ v Ty -> Σ _ \ ty' -> Σ _ \ Ty' ->  Σ (In {_} {ty'} Γ' v Ty') \ _ ->  Γ |- ty == ty' :: pTyU
  


postulate

  ==ctx-ext : {n : ℕ} {Γ Γ' : Ctx {n}} 
    -> Γ ==ctx Γ'
    -> {a a' : _} ->  Γ |- a == a' :: pTyU
    -> {A :  Γ |- a :: pTyU} {A' :  Γ' |- a' :: pTyU}
    -> Ext Γ A ==ctx Ext Γ' A'

  ==ctx-refl : {n : ℕ} {Γ : Ctx {n}} 
    -> Γ ==ctx Γ
    

  ==-trans :  {n : ℕ} {Γ : Ctx {n}} {a a' a'' aty : _}
    -> Γ |- a == a' :: aty ->  Γ |- a' == a'' :: aty
    -> Γ |- a == a'' :: aty
    
  ==-sym :  {n : ℕ} {Γ : Ctx {n}} {a a' aty : _}
    -> Γ |- a == a' :: aty 
    -> Γ |- a' == a :: aty


==-refl : {n : ℕ} {Γ : Ctx {n}}
    -> {a  aty : _ } 
    -> (A :  Γ |- a :: aty)
    -> Γ |- a == a :: aty
==-refl {n} {Γ} {a} {aty} A = joinV A A par-refl par-refl

preservation-ctx== :  {n : ℕ} {Γ Γ' : Ctx {n}} {a aTy : _}
  -> Γ |- a :: aTy -> Γ ==ctx Γ' 
  -> Γ' |- a :: aTy

preservation-ctx==-== :  {n : ℕ} {Γ Γ' : Ctx {n}} {a a' aTy : _}
  -> Γ |- a == a' :: aTy -> Γ ==ctx Γ' 
  -> Γ' |- a  == a' :: aTy
preservation-ctx==-== (joinV aTy a'Ty a~> a'~>) pctx = joinV (preservation-ctx== aTy pctx) (preservation-ctx== a'Ty pctx) a~> a'~>

preservation-ctx== (Var v {_} {aTY} x) pctx with pctx v x
... | aty' , aTY' , IN , joinV _ _  y z = Conv (Var v IN) (joinV aTY' (preservation-ctx== aTY pctx) z y)
preservation-ctx== (Pi aty bty) pctx = Pi (preservation-ctx== aty pctx) (preservation-ctx== bty (==ctx-ext pctx (==-refl aty)))
preservation-ctx==  (Fun ATy BTy bTy) pctx =
  Fun (preservation-ctx== ATy pctx)
    (preservation-ctx== BTy (==ctx-ext pctx (==-refl ATy)))
    (preservation-ctx== bTy (==ctx-ext (==ctx-ext pctx (==-refl ATy)) (==-refl (o (Pi ATy BTy)))))
preservation-ctx== (Conv aty eq) pctx = Conv (preservation-ctx== aty pctx) (preservation-ctx==-== eq pctx)
preservation-ctx== (App ty ty₁) pctx = App (preservation-ctx== ty pctx) (preservation-ctx== ty₁ pctx)
preservation-ctx== (Cast ty) pctx = Cast (preservation-ctx== ty pctx) -- (preservation-ctx== ty₁ pctx)
preservation-ctx== TyU pctx = TyU




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
regularity (Cast Ty ) = regularity Ty
regularity (Conv Ty (joinV _ x _ _)) = x

 

postulate
  stable-==-Pi1 : {n : ℕ} {Γ : Ctx {n}} {aty aty' : _}  {bty bty' : _} 
    -> Γ |-  pPi aty bty == pPi aty' bty' :: pTyU
    -> Γ |- aty == aty' :: pTyU
  
  stable-==-Pi2 : {n : ℕ} {Γ : Ctx {n}}  {aty aty' : _}  {bty bty' : _} 
    -> Γ |-  pPi aty bty == pPi aty' bty' :: pTyU
    -> {aTy' : Γ |- aty' :: pTyU}
    -> (Ext Γ aTy') |- bty ==  bty' :: pTyU

inv-Pi'' :  {n : ℕ} {Γ : Ctx {n}} {aty ty : _} {b : _} {bty  : _}
  -> Γ |- pFun b :: ty
  -> Γ |-  ty == pPi aty bty :: pTyU 
  -> Σ (Γ |- aty :: pTyU) \ aTy -> Σ (Ext Γ aTy |- bty :: pTyU) \ bTy -> Ext (Ext Γ aTy)  (o (Pi aTy bTy)) |- b :: po bty
inv-Pi'' {_} {Γ} {aty'} {_} {b} {bty'} (Fun {aty} {bty} {_} ATy BTy bTy) e@(joinV piTy pi'Ty _ _) = aTy' , BTy' , final
  where
    xx : Σ (Γ |- aty' :: pTyU) (λ z → Ext Γ z |- bty' :: pTyU)
    xx = inv-funTy' pi'Ty (==-refl TyU)
    
    aTy' : Γ |- aty' :: pTyU
    aTy' = proj₁ xx
    
    BTy' :  Ext Γ aTy' |- bty' :: pTyU
    BTy' = proj₂ xx

    
    almost : Ext (Ext Γ aTy') (o (Pi aTy' BTy')) |- b :: po bty
    almost = preservation-ctx== bTy (==ctx-ext (==ctx-ext ==ctx-refl (stable-==-Pi1 e) ) (o-== e))

    final : Ext (Ext Γ aTy') (o (Pi aTy' BTy')) |- b :: po bty'
    final = Conv almost (o-== ( stable-==-Pi2 e {_}))
    
inv-Pi'' (Conv ty x) eq = inv-Pi'' ty (==-trans x eq)

inv-Pi :  {n : ℕ} {Γ : Ctx {n}} {aty : _} {b : _} {bty  : _}
  -> Γ |- pFun b :: pPi aty bty 
  -> Σ (Γ |- aty :: pTyU)
           (λ aTy →
              Σ (Ext Γ aTy |- bty :: pTyU)
              (λ bTy →
                 Ext (Ext Γ aTy) (o (Pi aTy bTy)) |- b :: po bty))
inv-Pi {n} {Γ} {aty} {b} {bty} ty  = inv-Pi'' ty (==-refl ty-cond)
  where
    xx : Σ (Γ |- aty :: pTyU) (λ z → Ext Γ z |- bty :: pTyU)
    xx = inv-funTy ty

    ty-cond :  Γ |- pPi aty bty :: pTyU
    ty-cond = Pi (proj₁ xx) (proj₂ xx)



preservation~>p :  {n : ℕ} {Γ : Ctx {n}} {a a' aTy : _}
  -> Γ |- a :: aTy  -> a ~>p a'
  -> Γ |- a' :: aTy
preservation~>p (Pi ATy BTy) (par-Pi aty~> bty~>) =
  Pi (preservation~>p ATy aty~>)
    (preservation~>p (preservation-ctx== BTy (==ctx-ext ==ctx-refl (joinV ATy (preservation~>p ATy aty~>)  (par-step par-refl  aty~>) par-refl ))) bty~>)
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
preservation~>p  {_} {Γ} (App {_} {a} {aty} {bty} fTy aTy) (par-App {f} {f'} {a} {a'} f~> a~>)= {!!} -- final
  where 
    a'Ty : Γ |- a' :: aty
    a'Ty = preservation~>p aTy a~>
    
    f'a'Ty : Γ |- pApp f' a' :: (bty [ a' ])
    f'a'Ty = App (preservation~>p fTy f~>) a'Ty
    {-
    ATyTY : Γ |- aty :: pTyU
    ATyTY = proj₁ (inv-funTy fTy)
    Fwf : (Ext Γ ATyTY) |- bty :: pTyU
    Fwf = proj₂ (inv-funTy fTy)
    
    final : Γ |- pApp f' a' :: (bty [ a ])
    final = Conv f'a'Ty (joinV (subst-ty Fwf a'Ty) (subst-ty Fwf aTy) par-refl (par-step par-refl (sub-par (par-refll bty) a~>)))
    -}
    
preservation~>p (Cast aTy) (par-cast-red par) = preservation~>p aTy par
preservation~>p {_} {Γ} {pAnn a A} (Cast aty) (par-cast {_} {a'} {_} {A'} a-a' A-A') = final
  where
    a'ty : Γ |- a' :: A
    a'ty = preservation~>p aty a-a'

    -- get there with jsut regularity

    Aty = regularity aty
    A'ty : Γ |- A' :: pTyU
    A'ty = preservation~>p Aty A-A' -- why is this well founded?

   -- A'ty : Γ |- A' :: pTyU
   -- A'ty = preservation~>p Aty  A-A'

    a'ty' : Γ |- a' :: A'
    a'ty' = Conv a'ty (joinV Aty A'ty (par-step par-refl A-A') par-refl) 
    
    almost : Γ |- pAnn a' A' :: A'
    almost = Cast a'ty' --  A'ty
    final : Γ |- pAnn a' A' :: A
    final = Conv almost (joinV A'ty Aty par-refl (par-step par-refl A-A'))
  
  
preservation~>p (Conv Ty x) par = Conv (preservation~>p Ty par) x
preservation~>p (Var v x) par-Var = Var v x
preservation~>p TyU par-TyU = TyU

