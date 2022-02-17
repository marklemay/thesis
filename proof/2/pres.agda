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

-- ...




_==ctx_ : {n : ℕ} -> (Γ Γ' : pCtx {n}) -> Set
Γ ==ctx Γ' = {ty : _} -> {Ty : _}
  -> (v : Fin _)
  -> In  Γ v Ty -> Σ _ \ ty' -> Σ _ \ Ty' ->  Σ (In  Γ' v Ty') \ _ -> ty == ty'
  


preservation-ctx== :  {n : ℕ} {Γ Γ' : pCtx {n}} {a aTy : _}
  -> Γ |- a :: aTy -> Γ ==ctx Γ' 
  -> Γ' |- a :: aTy
preservation-ctx== (Var v x) eq = {!!}
preservation-ctx== TyU eq = {!!}
preservation-ctx== (Pi x x₁) eq = {!!}
preservation-ctx== (Fun x x₁ x₂) eq = {!!}
preservation-ctx== (App x x₁) eq = {!!}
preservation-ctx== (Ann x x₁) eq = Ann (preservation-ctx== x eq) (preservation-ctx== x₁ eq)
preservation-ctx== (Conv x x₁) eq = {!!}

preservation~>p :  {n : ℕ} {Γ : pCtx {n}} {a a' aTy : _}
  -> Γ |- a :: aTy  -> a ~>p a'
  -> Γ |- a' :: aTy
preservation~>p (Var v x) x₁ = {!!}
preservation~>p TyU x₁ = {!!}
preservation~>p (Pi x x₂) x₁ = {!!}
preservation~>p (Fun x x₂ x₃) x₁ = {!!}
preservation~>p (App x x₂) x₁ = {!!}
preservation~>p (Ann x x₂) (par-cast-red red) = preservation~>p x red
preservation~>p (Ann m M) (par-cast red aTy~>pty') = Conv (Ann (Conv (preservation~>p m red)
                                                                  (joinV (par-step par-refl aTy~>pty') par-refl)) (preservation~>p M aTy~>pty')) (joinV par-refl (par-step par-refl aTy~>pty'))
preservation~>p (Conv x x₂) x₁ = {!!}
