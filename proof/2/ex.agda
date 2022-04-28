{-# OPTIONS --type-in-type #-} 

module ex where

open import Data.Nat

* = Set

bot = (X : *) -> X

Unit = (X : *) -> X -> X
tt : Unit
tt = λ _ x → x

not : * -> *
not x = x -> bot

NatC = (X : *) -> (X -> X) -> X -> X

toC : ℕ -> NatC
toC zero = λ _ _ z → z
toC (suc n) = λ X s z → s (toC n X s z)

Even : NatC -> *
Even x = ((x *) not) Unit

Exists : (X : *) -> (Y : (X -> *)) -> *
Exists X Y = (C : *) -> ((x : X) -> Y x -> C) -> C

2e : Even (toC 2) 
2e = λ z → z (λ X z₁ → z₁)

2e' : Even (toC 2) 
2e' = λ s → s tt


-- 3e : Even (toC 3)
-- 3e = {!!}

4e : Even (toC 4)
4e = λ z → z (λ z₁ → z₁ (λ X z₂ → z₂))

anyeven : Exists NatC Even
anyeven = λ C z → z (λ X _ z₁ → z₁) (λ X z₁ → z₁)

anyeven' : Exists NatC Even
anyeven' = \ _ f -> f (toC 0) {!tt!}
