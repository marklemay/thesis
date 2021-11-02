module elab where

open import presyntax
open import bidir

import precast as c
import cast as c


open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])


data _|-_ELAB_:->:_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n}  -> c.PreSyntax {n} -> Set
data _|-_ELAB_:<-:_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n}  -> c.PreSyntax {n} -> Set


postulate
  _c~>p*_ :  {n : ℕ} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set



{-
  o : {n : ℕ} {a aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a :->: aTy -> {Ty : Γ |- ty :<-: pTyU}
    -> Ext Γ Ty |- po a :<-: po aTy
    
{-
  o-== : {n : ℕ} {a a' aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a == a' :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a == po a' :: po aTy
-}

-}

data _|-_ELAB_:->:_ {n} Γ  where
  Var : -- TODO could index 2 ctxs?
    (v : Fin n) -> {ty : _} -> c.In Γ v ty
    -> Γ |- (pVar v) ELAB (c.pVar v) :->: ty
  TyU : Γ |- pTyU ELAB (c.pTyU) :->: c.pTyU
  Ann : {m M : _} {a A : c.PreSyntax }
    -> Γ |- M ELAB A :<-: c.pTyU
    -> Γ |- m ELAB a :<-: A
    -> Γ |- (pAnn m M) ELAB a :->: A
    
  Pi : {M : _} {N : _} {A : _} {B : _}
    -> Γ |- M ELAB A :<-: c.pTyU
    -> c.Ext Γ A |- N ELAB B :<-: c.pTyU
    -> Γ |- (pPi M N) ELAB (c.pPi A B) :->: c.pTyU
    
  App : {m n : _} {b a : _} {C A : _} {B : _}
    -> Γ |- m ELAB b :->: C
    -> C c~>p* c.pPi A B
    -> Γ |- n ELAB a :<-: A
    -> Γ |- (pApp m n) ELAB (c.pApp b a) :->: (B c.[ a ])
    
data _|-_ELAB_:<-:_ {n} Γ  where

  Fun : {m : _} {b : _} {A : _} {B : _} -- {C A : _} {B : _}
    -> c.Ext (c.Ext Γ A)  (c.o (c.pPi A B)) |- m ELAB b :<-: (c.o B)
    -> Γ |- (pFun m) ELAB (c.pFun b) :<-: (c.pPi A B)

  Conv : {m : _} {a : _} {A : _} {B : _}
  -- extra conditions on b...?
    -> Γ |-  m ELAB a :->: A
    -> Γ |-  m ELAB (c.pCast a A B) :<-: B


data _|-ELAB_ : {n : ℕ} (Γ : Ctx {n}) -> c.Ctx {n} -> Set where
  emp-ELAB : Emp |-ELAB c.Emp
  ext-ELAB : {n : ℕ} {Γ : Ctx {n}} {H : c.Ctx {n}} {M : _} {A : _}
    -> Γ |-ELAB H
    -> H |- M ELAB A :<-: c.pTyU
    -> Ext Γ M |-ELAB c.Ext H A


{-
props:
erasure
well-cast
-}


reg<- : {n : ℕ} {H : c.Ctx {n}} {m : _} {A : _}
  -> c.CtxOK H 
  -> (H |- m ELAB A :<-: c.pTyU)
  -> (H c.|- A :: c.pTyU)
  
reg-> : {n : ℕ} {H : c.Ctx {n}} {m : _} {a A : _}
  -> c.CtxOK H 
  -> (H |- m ELAB a :->: A)
  -> (H c.|- A :: c.pTyU)

well-cast-> : {n : ℕ} {H : c.Ctx {n}}  {m : _} {a A : _}
  -> c.CtxOK H 
  -> (H |- m ELAB a :->: A)
  -> c._|-_::_ H a A

well-cast<- : {n : ℕ} {H : c.Ctx {n}}  {m : _} {a A : _}
  -> c.CtxOK H 
  -> c._|-_::_ H A c.pTyU
  -> (H |- m ELAB a :<-: A)
  -> c._|-_::_ H a A


reg-> ok (Var v x) = ok v _ x
reg-> ok TyU = c.TyU
reg-> ok (Ann x x₁) = reg<- ok x
reg-> ok (Pi x x₁) = c.TyU
reg-> {_} {H} ok (App {m } {n} {b} {a} {C} {A} {B} F ftyred Arg) = {!!}
  where
    fTy : H c.|- b :: c.pPi A B
    fTy = {!!} -- by conversion
    -- TODO
    BTy : H c.|- c.pPi A B :: c.pTyU
    BTy = c.reg ok fTy
    
    BTy' : c.Ext H A c.|- B :: c.pTyU
    BTy' = {!!} -- Pi inversion
    
    ATy : H c.|- A :: c.pTyU
    ATy = {!!} -- Pi inversion

    Arg' : H c.|- a :: A
    Arg' = well-cast<- ok ATy Arg 

    -- typed substitution


reg<- ok (Conv x) = c.Cast (well-cast-> ok x) (reg-> ok x) c.TyU    

-- TODO without ok or c.reg? don't think this is possible
well-cast<- {_} {H} ok ty (Fun {m } {b} {A} {B} e) = c.Fun (well-cast<- {!!} BTy' e) -- by ext wf
  where
    BTy : c.Ext H A c.|- B :: c.pTyU
    BTy = {!!} -- pi inversion on ty

    BTy' : c.Ext (c.Ext H A) (c.o (c.pPi A B)) c.|- c.o B :: c.pTyU
    BTy' = {!!} -- weaken


well-cast<- ok ty (Conv e) = c.Cast (well-cast-> ok e) (reg-> ok e) ty

well-cast-> ok (Var v x) = c.Var v x
well-cast-> ok TyU = c.TyU
well-cast-> ok (Ann ty bod) = well-cast<- ok (well-cast<- ok c.TyU ty) bod
well-cast-> ok (Pi A B) = c.Pi (well-cast<- ok c.TyU A) (well-cast<- {!!}  c.TyU B) -- by ext wf
well-cast->  {_} {H} ok (App {m } {n} {b} {a} {C} {A} {B} F ftyred Arg) = ans
  where
    fTy : H c.|- b :: c.pPi A B
    fTy = {!!} -- by conversion
    
    BTy : H c.|- c.pPi A B :: c.pTyU
    BTy = c.reg ok fTy
    
    ATy : H c.|- A :: c.pTyU
    ATy = {!!} -- Pi inversion

    ans : H c.|- c.pApp b a :: (B c.[ a ])
    ans =  c.App fTy (well-cast<- ok ATy Arg) -- TODO wf


{-
bidirection elabs

well-cast<- (Fun argTy bodTy bod) --  MTy
  with well-cast<- bod  --| well-cast<- argTy | well-cast<- bodTy | 
... | fst , fst₁ , fst₂ , fst₃ , bodElab = {!!} , ({!!} , ({!!} , ({!!} , (Fun {!!}))))
well-cast<- (Conv x x₁ mTy) -- MTy
  = {!!}

well-cast-> = {!!}
-}


record out->  {n : ℕ} (Γ : Ctx {n}) (m M : PreSyntax {n}) : Set where
  field
    H : c.Ctx {n}
    a A : c.PreSyntax {n}
    ctxElab : Γ |-ELAB H
    elab : H |- m ELAB a :->: A
 --  (H |- M ELAB A :<-: c.pTyU)
record out<-  {n : ℕ} (Γ : Ctx {n}) (m M : PreSyntax {n}) : Set where
  field
    H : c.Ctx {n}
    a A : c.PreSyntax {n}
    ctxElab : Γ |-ELAB H
    elab : H |- m ELAB a :<-: A

postulate
  in-both : {n : ℕ}{Γ : Ctx {n}} {H : c.Ctx {n}} 
    -> Γ |-ELAB H
    -> (v : Fin n)
    -> {M : PreSyntax {n}}
    -> In Γ v M
    -> Σ (c.PreSyntax {n}) λ A → c.In H v A × H |- M ELAB A :<-: c.pTyU

bi-elabs-ctx : {n : ℕ}
  -> (Γ : Ctx {n})
  -> Σ (c.Ctx {n}) λ H → Γ |-ELAB H

bi-elabs-> : {n : ℕ} {Γ : Ctx {n}} {m M : PreSyntax {n}}
  -> Γ |- m :->: M 
  -> out-> Γ m M

bi-elabs<- : {n : ℕ} {Γ : Ctx {n}} {m M : PreSyntax {n}}
  -> Γ |- m :<-: M
  -> out<- Γ m M



bi-elabs-> {_} {Γ} (Var x v lkup) with bi-elabs-ctx Γ
bi-elabs-> {_} {Γ} (Var x v lkup) | H' , ΓElabH with in-both ΓElabH v lkup
bi-elabs-> {_} {Γ} (Var x v lkup) | H' , ΓElabH | fst , fst₁ , snd = record { H = H' ; a = c.pVar v ; A = fst ; ctxElab = ΓElabH ; elab = Var v fst₁ }
bi-elabs-> {_} {Γ} (TyU _) with bi-elabs-ctx Γ
... | H' , ΓElabH = record { H = H' ; a = c.pTyU ; A = c.pTyU ; ctxElab = ΓElabH ; elab = TyU }
bi-elabs-> (Ann BTy B) with bi-elabs<- B | bi-elabs<- BTy
... | record { H = H ; a = a ; A = A ; ctxElab = ctxElab ; elab = elab } | yy = record { H = {!!} ; a = {!!} ; A = {!!} ; ctxElab = {!!} ; elab = Ann {!!} elab }
bi-elabs-> (Pi aTy bodTy) = {!!}
bi-elabs-> (App x x₁) = {!!}
bi-elabs<- = {!!}

bi-elabs-ctx = {!!} -- bidierctional reg
