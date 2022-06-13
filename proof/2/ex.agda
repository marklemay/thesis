{-# OPTIONS --type-in-type #-} 

module ex where

open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality hiding ([_])

* = Set

bot = (X : *) -> X

Unit = (X : *) -> X -> X
tt : Unit
tt = λ _ x → x

not : * -> *
not x = x -> bot

NatC = (X : *) -> (X -> X) -> X -> X

-- to debug with arabic numerals
toC : ℕ -> NatC
toC zero = λ _ _ z → z
toC (suc n) = λ X s z → s (toC n X s z)

fromC : NatC -> ℕ
fromC n = n ℕ suc zero

toFromTest : fromC (toC 5) ≡ 5
toFromTest = refl

_+_ : NatC -> NatC -> NatC
x + y = \ X s z -> x X s (y X s z)

addtest : ((toC 2) + (toC 3)) ≡ (toC 5)
addtest = refl

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
anyeven' = \ _ f -> f (toC 0) tt


-- check chapter 3 claim

xp1Is1px : (x : NatC) -> (toC 1) + x ≡ x + (toC 1)
xp1Is1px x = {!!}
-- even with eta not a def eq 



-- example from discord

Bool = (A : *) -> A -> A -> A

True : Bool
True _ t f = t

False : Bool
False _ t f = f

--indBool : (P : Bool -> * ) -> P True -> P False -> (b : Bool) -> P b
--indBool P t f b = b (P b) t f



-- Liebnitz Eq
_~~_ : {X : * } -> X -> X -> *
_~~_ {X} x x' = (C : (X -> *)) -> C x -> C x'

reflL : {X : * } -> (x : X) -> x ~~ x
reflL _ = λ _ z → z


symL : {X : * } -> (x : X) -> (x' : X) -> x ~~ x' -> x' ~~ x
symL x x' = λ p C → p (λ xx → (C xx) → C x) (λ xx → xx)

transL : {X : * } -> (x : X) -> (x' : X)  -> (x'' : X) -> x ~~ x' -> x' ~~ x'' -> x ~~ x''
transL x x' x'' = λ p pp C cx → pp C (p C cx)
