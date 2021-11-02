module elab where

open import presyntax
open import bidir

import precast as c
import cast as c

import syn-paper as t


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


data _|-ELAB_ : {n : ℕ} (Γ : pCtx {n}) -> c.Ctx {n} -> Set where
  emp-ELAB : pEmp |-ELAB c.Emp
  ext-ELAB : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} {M : _} {A : _}
    -> Γ |-ELAB H
    -> H |- M ELAB A :<-: c.pTyU
    -> pExt Γ M |-ELAB c.Ext H A


{- TODO seperate file?
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

data _Erase_ {n : ℕ} : (PreSyntax {n}) -> c.PreSyntax {n} -> Set where

  eVar : (i : Fin n) -> (pVar i) Erase (c.pVar i)
  eTyU :  pTyU Erase c.pTyU
  -- ePi :  (aTy : PreSyntax {n}) -> (bodTy :  PreSyntax {suc n}) -> PreSyntax
  --eFun : (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  --eApp :  (f : PreSyntax {n}) -> (a : PreSyntax {n}) -> PreSyntax
  --eAnn :  (e : PreSyntax {n}) -> (ty : PreSyntax {n}) -> PreSyntax
  --eCast


record out->  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H) {m M : PreSyntax {n}} (ty : Γ |- m :->: M) : Set where
  field
    a A : c.PreSyntax {n}
    elab : H |- m ELAB a :->: A

record out<-  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H)  (m M : PreSyntax {n}) : Set where
  field
    a A : c.PreSyntax {n}
    elab : H |- m ELAB a :<-: A
    elabTy : H |- M ELAB A :<-: c.pTyU

postulate
  in-both : {n : ℕ}{Γ : pCtx {n}} {H : c.Ctx {n}} 
    -> Γ |-ELAB H
    -> (v : Fin n)
    -> {M : PreSyntax {n}}
    -> In Γ v M
    -> Σ (c.PreSyntax {n}) λ A → c.In H v A × H |- M ELAB A :<-: c.pTyU


bi-elabs-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :->: M)
  -> out-> ctxElab ty

bi-elabs<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> Γ |- m :<-: M
  -> out<- ctxElab m M

bi-elabs<-TyU : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : PreSyntax {n}}
  -> Γ |- M :<-: pTyU
  -> Σ _ λ A → H |- M ELAB A :<-: c.pTyU


bi-elabs-> {_} {Γ} ctxElab (Var x v lkup) with in-both ctxElab v lkup
bi-elabs-> {_} {Γ} ctxElab (Var x v lkup) | fst , fst₁ , snd
  = record { a = c.pVar v ; A = fst ; elab = Var v fst₁ }
bi-elabs-> ctxElab (TyU x) = record { a = c.pTyU ; A = c.pTyU ; elab = TyU }
bi-elabs-> ctxElab (Ann MTy M) with bi-elabs<- ctxElab M
... | record { a = a ; A = A ; elab = am ; elabTy = tyum } = record { a = a ; A = A ; elab = Ann tyum am }
bi-elabs-> ctxElab (Pi argTy bodTy) with bi-elabs<-TyU ctxElab argTy | bi-elabs<-TyU  {!!} bodTy -- elab extention
... | A , Aelab | B , BElab = record { a = c.pPi A B ; A = c.pTyU ; elab = Pi Aelab {!BElab!} }
bi-elabs-> ctxElab (App F Arg) with bi-elabs-> ctxElab F | bi-elabs<- ctxElab Arg
... | record { a = b ; A = B ; elab = Felab } | record { a = a ; A = A ; elab = elab ; elabTy = elabTy }
 = record { a = c.pApp b a ; A = {!!} ; elab = App Felab {!!} elab }
 -- needs erasure of typse, for conversion

bi-elabs<- ctxElab (Fun x x₁ x₂) = record { a = c.pFun {!!} ; A = {!c.Pi!} ; elab = Fun {!!} ; elabTy = {!Pi!} }
bi-elabs<- ctxElab (Conv under _ ty) with bi-elabs-> ctxElab under | bi-elabs<-TyU ctxElab ty
... | record { a = a ; A = A ; elab = elab } | fst , snd = record { a = c.pCast a A fst ; A = fst ; elab = Conv elab ; elabTy = snd }
-- suspends allmost all evaluation

bi-elabs<-TyU ctxElab (Conv under _ ty) with bi-elabs-> ctxElab under
... | record { a = a ; A = A ; elab = elab } = c.pCast a A c.pTyU , Conv elab

-- elaboration from bi has == conversions?
-- if |- M : * and M Elab C and if M ~>* (A -> B) then C ~>* (A' -> B')

consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :->: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → c c~>p* c.pPi A B
  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :<-: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → c c~>p* c.pPi A B


consistent-lemma ctxElab (Var x .v x₂) (Var v x₁) = {!!}  {!!} , ({!!} , {!!}) -- by erasure of the lookup ctxElab
consistent-lemma ctxElab (Ann x x₃) (Ann x₁ x₂) = consistent-lemma<- ctxElab x₃  x₂
consistent-lemma ctxElab x (App e x₁ x₂) = {!!}
-- must be that, bodTy [ a₁ ] ≟ pPi M₁ N₁
-- thus bodTy ≟ pPi M₁' N₁' and folloews by (mutual?) induction
-- or  bodTy = x, a₁ ≟ pPi M₁ N₁ and folloews by (mutual?) induction

consistent-lemma<- ctxElab (Fun x x₁ x₂) (Fun e) = {!!} -- directly
consistent-lemma<- ctxElab (Conv x x₂ x₃) (Conv x₁) = {!!}
 --by def of ==, , induction on sub-der
{-
consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ t.|- m :: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → c c~>p* c.pPi A B
  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ t.|- m :: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → c c~>p* c.pPi A B


consistent-lemma ctxElab (t.Var .v x) (Var v x₁) = {!!} , ({!!} , {!!}) -- by erasure of the lookup ctxElab
consistent-lemma ctxElab (t.Ann x) (Ann x₁ x₂) = consistent-lemma<- ctxElab x x₂
consistent-lemma ctxElab x (App e x₁ x₂) = {!!}
-- must be that, bodTy [ a₁ ] ≟ pPi M₁ N₁
-- thus bodTy ≟ pPi M₁' N₁' and folloews by (mutual?) induction
-- or  bodTy = x, a₁ ≟ pPi M₁ N₁ and folloews by (mutual?) induction


-- other syntax would need to be typed by conversion
consistent-lemma ctxElab (t.Conv x x₂) e = {!!} --by def of ==, , induction on sub-der

consistent-lemma<- ctxElab (t.Fun x) (Fun e) = {!!} -- directly
consistent-lemma<- ctxElab x (Conv x₁) = {!!}
-- need to show that the type underlieing the cast is Pi
-- ????!!!!!!!

consistent-lemma<- ctxElab (t.Conv x x₁) e = {!!} --by def of ==, , induction on sub-der

-}
{-
consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m : PreSyntax {n}}
  -> Γ t.|- m :: pTyU
  -> {M : _} {N : _}
  -> m ~>p* pPi M N
  -> m ~>p* pPi M N
  -> {!Σ ? ?!}
consistent-lemma = {!!}
--  m ~>p* pPi M N
-}

bi-elabs-ctx : {n : ℕ}
  -> (Γ : pCtx {n})
  -> Σ (c.Ctx {n}) λ H → Γ |-ELAB H
bi-elabs-ctx = {!!} -- bidierctional reg
