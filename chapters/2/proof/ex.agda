{-# OPTIONS --type-in-type #-}

module ex where

* = Set

Bot : *
Bot = (X : *) -> X

Unit : *
Unit = (X : *) -> X -> X

tt : Unit
tt = λ X z → z

Bool : *
Bool = (X : *) -> X -> X -> X

true : Bool
true = \ _ x _ -> x

false : Bool
false = \ _ _ x -> x

not : Bool -> Bool
not = \ b -> b Bool false true

and : Bool -> Bool -> Bool
and = \ x y -> x Bool y false

Nat : *
Nat = (X : *) -> (X -> X) -> X -> X

zero : Nat 
zero = \ _ _ z -> z
one : Nat
one = \ _ s z -> s z

two : Nat
two = \ _ s z -> s (s z)


suc : Nat -> Nat
suc = \ n -> \ X s z -> s (n X s z)

_+_ : Nat -> Nat -> Nat
x + y = λ X s z → x X s (y X s z)

pred : Nat -> Nat
pred = \ n X s z -> n ((X → X) → X) (\ g h -> h (g s)) (\ u -> z) (\u -> u)

tuple : (A : *) -> (B : *) -> *
tuple = λ A B → (X : *) -> (A -> B -> X) -> X

fst : (A : *) -> (B : *) -> tuple A B -> A
fst =  λ A B z → z A (λ z₁ _ → z₁)

snd : (A : *) -> (B : *) -> tuple A B -> B
snd = λ A B z → z B (λ _ z₁ → z₁)

mkTuple : (A : *) -> (B : *) -> (a : A) -> (b : B) -> tuple A B
mkTuple = λ A B a b X z → z a b


or : (A : *) -> (B : *) -> *
or = λ A B → (X : *) -> (A -> X) -> (B -> X) -> X

elimor :  (A : *) -> (B : *) -> or A B -> (X : *) -> (A -> X) -> (B -> X) -> X
elimor = λ A B z → z

left : (A : *) -> (B : *) -> (a : A) -> or A B
left = λ A B a X z _ → z a

right : (A : *) -> (B : *) -> (b : B) -> or A B
right = λ A B b X _ z → z b

pred' : Nat -> or Unit Nat
pred' = \ n ->
  n (or Unit Nat) (λ x → x (or Unit Nat) (λ _ → right Unit Nat zero) \ x -> right Unit Nat (suc x)) (left Unit Nat tt)

Neg : * -> *
Neg = \ X -> X -> Bot

Even : Nat -> *
Even = \ n -> n * (λ x → Neg x) Unit

pr-e0 : Even zero
pr-e0 = λ X → λ z → z


pr-e2 : Even two
pr-e2 = λ z → z (λ X z → z)

Div : Nat -> Nat -> *
Div = \ n d -> {!!}

Eq : (A : *) -> (a a' : A) -> *
Eq = λ A a a' → (C : (A ->  *)) -> C a -> C a' 

r :(A : *) -> (a : A) -> Eq A a a
r = λ A a C z → z

sym : (A : *) -> (a a' : A) -> Eq A a a' -> Eq A a' a
sym = λ A a a' z C → z (λ z₁ → C z₁ → C a) (λ x → x)

trans : (A : *) -> (a a' a'' : A) -> Eq A a a' -> Eq A a' a'' -> Eq A a a'' 
trans = λ A a a' a'' z z₁ C z₂ → z₁ C (z C z₂)

cong : (A : *) -> (B : *) -> (f : A -> B) -> (a a' : A) -> Eq A a a' -> Eq B (f a) (f a') 
cong = λ A B f a a' z C → z (λ z₁ → C (f z₁))


case : (n : Nat) -> (X : *) -> X -> (Nat -> X) -> X
case = λ n X x x₁ → {!b!} 

dcase : (n : Nat) -> (P : Nat -> *) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> P n
dcase = {!!}





Nat-ind : (P : Nat -> *) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
Nat-ind = {!!}

Bool-ind : (P : Bool -> *) -> P true -> P false -> (n : Bool) -> P n
Bool-ind = λ P x x₁ n → {!!}

prz-nn : (b : Bool) -> Eq Bool b (not (not b))
prz-nn = λ b → {!!}

-- funny, I think this unintentionally follows by eta expansion
-- λ X s z → n X s z
-- λ X s z → n X s z
prz-com : (n : Nat) -> Eq Nat (n + zero) (zero + n)
prz-com = {!!}

postulate
  n : Nat
