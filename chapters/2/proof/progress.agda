module progress where



open import presyntax
open import syn

open import Data.Nat
open import Data.Fin
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])



trans-== : {n : ℕ} {Γ : Ctx {n}} {a b c ty : _}
    -> Γ |- a == b :: ty
    -> Γ |- b == c :: ty
    -> Γ |- a == c :: ty
trans-== = {!!}
{-
trans-== (join {n} an bn) (join {m} bm cm) with confulent-~>* bn bm
trans-== (join {n} an bn) (join {m} bm cm) | o , mo , n~>o = join {_} {_} {o} (trans-~>*  an mo) (trans-~>*  cm n~>o)
-}


refl-== : {n : ℕ} {Γ : Ctx {n}} {a ty : _}
    -> Γ |- a :: ty
    -> Γ |- a == a :: ty
refl-== x = joinV x x par-refl par-refl


data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU : pTyU val
  vPi : { aTy : PreSyntax } -> {bodTy : PreSyntax }
     -> (pPi aTy bodTy) val
  vFun : {bod : PreSyntax {suc (suc n)} }
    -> (pFun bod) val
  -- TODO should casts be values?

data  _~>_ {n : ℕ} : PreSyntax {n} ->  PreSyntax {n} -> Set where
  app-red : {a  : PreSyntax {n}} ->  {bod : PreSyntax {suc (suc n)} }
    ->  a val
    -> (pApp (pFun bod)  a) ~> ( bod [ po (pFun  bod) ] [ a ]  )
    
  cast-red : {e : PreSyntax} -> {ty : PreSyntax}
    ->  e val
    -> (pAnn e ty) ~> e
    
  -- structural
  appf-struc : {f f' a : PreSyntax } -> f ~> f' -> pApp f a ~> pApp f' a
  appa-struc : {f a a' : PreSyntax } -> f val -> a ~> a' -> pApp f a ~> pApp f a'
  
  cast-struc : {e e' : PreSyntax} -> {ty : PreSyntax}
    ->  e ~> e' 
    -> (pAnn e ty) ~> (pAnn e' ty) 



stable-tyu :  {n : ℕ} {a : PreSyntax {n}}
   -> pTyU ~>p* a 
   -> a ≡ pTyU
stable-tyu par-refl = refl
stable-tyu (par-step rest step) with stable-tyu rest
stable-tyu (par-step rest par-TyU) | refl = refl


stable-pi :  {n : ℕ}  {a aTy : PreSyntax {n}} {bodTy : _}
   ->  pPi aTy bodTy ~>p* a 
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy' -> a ≡ pPi aTy' bodTy' × aTy ~>p* aTy' × bodTy ~>p* bodTy'
stable-pi par-refl = _ , _ , refl , par-refl , par-refl
stable-pi (par-step front step) with stable-pi front
stable-pi (par-step front (par-Pi  aty'~aty'' bodTy'~bodTy'')) | aty' , bty' , refl , aty~aty' , bodTy~bodTy'
  = _ , _ ,  refl ,
      par-step aty~aty' aty'~aty'' ,
      par-step bodTy~bodTy' bodTy'~bodTy''


stable-pi' :  {n : ℕ}  {a aTy : PreSyntax {n}} {bodTy : _}
   ->  pPi aTy bodTy ~>p* a 
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy' -> a ≡ pPi aTy' bodTy'
stable-pi' x with stable-pi x
... | fst , fst₁ , fst₂ , _ = fst , fst₁ , fst₂


tyu=/=pi : {n : ℕ} {Γ : Ctx {n}} {aty ty : _} {bodTy : _}
    -> ¬ Γ |- pTyU == pPi aty bodTy :: ty
tyu=/=pi (joinV  _ _ an bn) = {!!}
{-
tyu=/=pi (joinV  _ _ an bn) with stable-tyu an
tyu=/=pi (joinV {.pTyU} an bn) | refl with stable-pi' bn
tyu=/=pi (joinV {.pTyU} an bn) | refl | ()
-}


canonical-form-pi : {m pi aTy : _} -> {bodTy : _}
  -> Emp |- m :: pi -> m val
  -> Emp |- pi == pPi aTy bodTy :: pTyU
  ->  Σ _ \ bod  -> m ≡ pFun bod
canonical-form-pi = {!!}
{-
canonical-form-pi (Conv der x) vTyU eq = canonical-form-pi der vTyU (trans-==  x eq)
canonical-form-pi (Conv der x) vPi eq = canonical-form-pi  der vPi (trans-==  x eq)
canonical-form-pi TyU vTyU eq = ⊥-elim (tyu=/=pi eq) --!
canonical-form-pi (Pi der der₁) vPi eq = ⊥-elim (tyu=/=pi eq) --!
canonical-form-pi der (vFun {bod}) eq = bod , refl
-}


progress : {m n : _} -> Emp |- m :: n -> m val ⊎ Σ PreSyntax \ m' -> m ~> m'
progress TyU = inj₁ vTyU
progress (Pi x x₁) = inj₁ vPi
progress (Fun x x₁ x₂) = inj₁ vFun
progress (Conv x x₁) = progress x
progress (App fDer aDer)  with progress fDer | progress aDer
progress (App {f} {a} fDer aDer) | inj₂ (f' , f~>f') | _ = inj₂ (pApp f' a , appf-struc f~>f' )
progress (App {f} {a} fDer aDer) | inj₁ fval | inj₂ (a' , a~>a') = inj₂ (pApp f a' , appa-struc fval a~>a')
progress (App {f} {a} fDer aDer) | inj₁ fval | inj₁ aval with canonical-form-pi fDer fval (refl-== ({!!}))
progress (App {_} {a} fDer aDer) | inj₁ fval | inj₁ aval | bod , refl = inj₂ ((bod [ po (pFun bod) ] [ a ]) , app-red aval)
progress (Cast x) with progress x
progress (Cast x) | inj₁ x₁ = inj₂ (_ , cast-red x₁)
progress (Cast x) | inj₂ (e , step) = inj₂ (pAnn e _ , cast-struc step)
