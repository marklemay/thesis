{-# OPTIONS --type-in-type #-} 

module ex2 where

open import Data.Nat hiding (_+_)
open import Data.Bool

open import Relation.Binary.PropositionalEquality hiding ([_])


exx2 : _≡_ {_} {ℕ -> ℕ} (\ x -> x) (\ x -> x)
exx2 = refl


exx3 : _≡_ {_} {Bool -> Bool} (\ x -> x) (\ y -> y)
exx3 = refl


exx4 : _≡_ {_} {Bool -> Bool} (λ { true → true ; false → false }) (λ { true → true ; false → false })
exx4 = {!!}

f : ℕ -> ℕ
f x = x

g : ℕ -> ℕ
g x = x

exx5 : _≡_ {_} {ℕ -> ℕ} (\ x -> x) f
exx5 = refl

exx6 : _≡_ {_} {ℕ -> ℕ} f g
exx6 = refl


h : ℕ -> ℕ
h = \ x -> x

exx7 : _≡_ {_} {ℕ -> ℕ} f h
exx7 = refl


boolOrNat : Bool -> Set
boolOrNat true = Bool
boolOrNat false = ℕ

data bot : Set where

boolOrBot : Bool -> Set
boolOrBot false = Bool
boolOrBot true = bot

ex8 : (b : Bool) -> boolOrBot b -> ℕ
ex8 false y = 9



