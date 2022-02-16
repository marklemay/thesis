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



preservation~>p :  {n : ℕ} {Γ : Ctx {n}} {a a' aTy : _}
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
