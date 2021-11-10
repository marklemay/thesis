module bidir where

open import presyntax

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

-- untyped definitional eq
data  _~~_ {n : ℕ} : PreSyntax {n} -> PreSyntax {n} -> Set where
  joinV : {n m m' : _}
    -> m ~>p* n
    -> m' ~>p* n
    -> m ~~ m'

--  Ctx  : ℕ -> Set -- assume ctxs were well formed by consnstruction
--  Emp : Ctx 0

postulate --  TODO is equivelence defifned in the std lib?
  refl~~ :  {n : ℕ} -> {x : PreSyntax {n}} -> x ~~ x
  trans~~ :  {n : ℕ} -> {x y z : PreSyntax {n}} -> x ~~ y -> y ~~ z -> x ~~ z



-- data Ctx : {n : ℕ} -> Set
data _|-_:<-:_ {n : ℕ} (Γ : pCtx {n}) : PreSyntax {n} -> PreSyntax {n} -> Set
data _|-_:->:_ {n : ℕ} (Γ : pCtx {n}) : PreSyntax {n} -> PreSyntax {n} -> Set

{-
-- in agda it makes sense to work in mutially well formed contexts
data Ctx where
  Emp : Ctx {zero}
  Ext : {n : ℕ} {a : PreSyntax {n}} -> (Γ : Ctx) -> Γ |- a :<-: pTyU -> Ctx {suc n}

data WFCtx : {n : ℕ} -> pCtx {n} -> Ctx {n} -> Set where
  EmpWF : WFCtx pEmp Emp
  ExtWF : {n : ℕ} {Γ : _} {H : _} {a : PreSyntax {n}}
    -> WFCtx H Γ
    -> (awf : Γ |- a :<-: pTyU)
    -> WFCtx (pExt H a) (Ext Γ awf)
-}


CtxOK : {n : ℕ} -> (Γ : pCtx {n}) -> Set
CtxOK Γ = (v : _) -> (ty : _ ) -> In Γ v ty -> Γ |- ty :<-: pTyU




data _|-_:->:_ {n} Γ  where
  Var : CtxOK  Γ
    -> (v : Fin n) -> {ty : _}
    --  -> {Ty : _} -> In {_} {ty} Γ v Ty ->
    -> In Γ v ty
    -> Γ |- pVar v :->: ty
  TyU : CtxOK  Γ
    -> Γ |- pTyU :->: pTyU
  Ann : {ty : PreSyntax }
    -> Γ |-  ty :<-: pTyU
    ->  {e : PreSyntax } -> Γ |-  e :<-: ty
    -> Γ |-  pAnn e ty :->: ty
  Pi : {aty : PreSyntax } -> {bodty : PreSyntax }
    -> (aTy : Γ  |- aty :<-: pTyU)
    -> (bodTy : pExt Γ aty |- bodty :<-: pTyU)
    -> Γ |-  pPi aty bodty :->: pTyU
  App : {f a aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |- f :->: pPi aTy bodTy
    -> Γ |- a :<-: aTy 
    -> Γ |- pApp f a  :->: (bodTy [ a ])

-- ->  means we insist on coming to the answer without converions, instead we need to meadiate underlieng conversions with annotations 
-- this is a littel dumb in real life  |- M :<-: * might require |- m :: (M::*) instead of |- m::M 

-- note in chapter 3 that <- matches every source location (TODO missing on the type posintion of annotaion?)

data _|-_:<-:_ {n} Γ  where
  Fun : { aty : PreSyntax }
    -> (aTy : Γ  |- aty :<-: pTyU)
    -> {bodty : PreSyntax }
    -> (bodTy : pExt Γ aty |- bodty :<-: pTyU)
    -> {Γ |-  pPi aty bodty :->: pTyU}
    -> {bod : PreSyntax }
    -> pExt (pExt Γ aty)  (po (pPi aty bodty)) |- bod :<-: po bodty
    -> Γ |- pFun bod :<-: pPi aty bodty
    -- TODO discuss that funs take types that are not directly convertable, and thus require annotations
    -- thjis is standard as per https://www.cl.cam.ac.uk/~nk480/bidir-survey.pdf (Coqrand whnfed it)
    -- the implementation is more libral and will atempt to evaluate to WHNF
    
  Conv : {a m m' : PreSyntax }
    -> Γ |- a :->: m
    -> m ~~ m'
    -> Γ |- m' :<-: pTyU
    -> Γ |- a :<-: m'


-- if there's an check we know a bit about how it has to look
data B-Inv<- {n : ℕ} : (m M : PreSyntax {n}) -> Set where
  Fun-Inv : {bod : PreSyntax } { aty : PreSyntax } {bodty : PreSyntax }
    -> B-Inv<- bod (po bodty)
    -> B-Inv<- (pFun bod) (pPi aty bodty)

  RestVar : {v : _} {M : PreSyntax } -> B-Inv<- (pVar v) M
  RestTyU : {M : PreSyntax } -> B-Inv<- pTyU M
  RestAnn : {m M N : PreSyntax } -> B-Inv<- (pAnn m M) N
  RestPi : {m : _} {M : _} {N : _} -> B-Inv<- (pPi N M) m
  RestApp : {m : _} {M : _} {N : _} -> B-Inv<- (pApp N M) m


inv<- : {n : ℕ} {Γ : pCtx {n}} {m M : PreSyntax }
    -> Γ |- m :<-: M
    -> B-Inv<- m M
inv<- (Fun x x₁ Bod) = Fun-Inv (inv<- Bod)
inv<- (Conv (Var x v x₃) x₁ x₂) = RestVar
inv<- (Conv (TyU x) x₁ x₂) = RestTyU
inv<- (Conv (Ann x x₃) x₁ x₂) = RestAnn
inv<- (Conv (Pi aTy bodTy) x₁ x₂) = RestPi
inv<- (Conv (App x x₃) x₁ x₂) = RestApp




-- Need lemma?
-- if | m <- M  then exists m' = m st | m' -> M
-- super helpful
-- if |- m <- M then there exixts M' = M s.t. |- M' -> *

postulate
  o<-Ty : {n : ℕ} {Γ : pCtx {n}} {m M : PreSyntax }
    -> Γ |- m :<-: M
    -> {W : _}
    -> pExt Γ W |- po m :<-: po M

  swapzies<- : {n : ℕ} {Γ : pCtx {n}} {m M : PreSyntax }
    -> Γ |- m :<-: M
    -> Σ _ λ M' → (Γ |- m :<-: M') × (Γ |- M' :->: pTyU)
  swapzies-> : {n : ℕ} {Γ : pCtx {n}} {m M : PreSyntax }
    -> Γ |- m :->: M
    -> Σ _ λ M' → (Γ |- m :<-: M') × (Γ |- M' :->: pTyU)

  swapzies~~<- : {n : ℕ} {Γ : pCtx {n}} {m M : PreSyntax }
    -> Γ |- M :<-: pTyU
    -> Σ _ λ M' → (M ~~ M') × (Γ |- M' :->: pTyU)

{-

__ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

_,′_ : A → B → A × B
_,′_ = _,_

------------------------------------------------------------------------
-- Existential quantifiers

∃ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _
-}
{-
TODO
 well typed
 regularity
 conservative
-}
