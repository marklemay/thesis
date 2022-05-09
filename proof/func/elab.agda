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


data _|-_ELAB_:->:_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set
data _|-_ELAB_:<-:_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set


postulate
  _c~>p*_ :  {n : ℕ} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set

  o-> : {n : ℕ} {m : _} {a : _} {aTy : _} {ty : _} {Γ : c.Ctx {n}} -> Γ |- m ELAB a :->: aTy
    -> c.Ext Γ ty |- po m ELAB c.o a :->: c.o aTy
    {-
  o-== : {n : ℕ} {a a' aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a == a' :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a == po a' :: po aTy
-}


data _|-_ELAB_:->:_ {n} Γ  where
  Var : -- TODO could index 2 ctxs?
    (v : Fin n) -> {ty : _} -> c.In Γ v ty
    -> Γ |- (pVar v) ELAB (c.pVar v) :->: ty
  TyU : Γ |- pTyU ELAB (c.pTyU) :->: c.pTyU
  Ann : {m M : _} {a A : c.PreSyntax }
    -> Γ |- M ELAB A :<-: c.pTyU --does this make it not well cast anymore?
    -> Γ |- m ELAB a :<-: A
    -> Γ |- (pAnn m M) ELAB a :->: A
    
  Pi : {M : _} {N : _} {A : _} {B : _}
    -> Γ |- M ELAB A :<-: c.pTyU
    -> c.Ext Γ A |- N ELAB B :<-: c.pTyU
    -> Γ |- (pPi M N) ELAB (c.pPi A B) :->: c.pTyU
    
  App : {m n : _} {b a : _} {A : _} {B : _}
 --   -> Γ |- m ELAB b :->: C
 --   -> C c~>p* c.pPi A B
    -> Γ |- m ELAB b :->: c.pPi A B
    -> Γ |- n ELAB a :<-: A
    -> Γ |- (pApp m n) ELAB (c.pApp b a) :->: (B c.[ a ])
    
data _|-_ELAB_:<-:_ {n} Γ  where

  Fun : {m : _} {b : _} {A : _} {B : _} -- {C A : _} {B : _}
    -> c.Ext (c.Ext Γ A)  (c.o (c.pPi A B)) |- m ELAB b :<-: (c.o B)
    -> Γ |- (pFun m) ELAB (c.pFun b) :<-: (c.pPi A B)

  Cast : {m : _} {a : _} {A : _} {B : _}
  -- extra conditions on b...?
    -> Γ |- m ELAB a :->: A
    -> Γ |- m ELAB (c.pCast a A B) :<-: B

  Conv-* : {m : _} {a : _}
    -> Γ |- m ELAB a :->: c.pTyU
    -> Γ |- m ELAB a :<-: c.pTyU




elabCast-> : {n : ℕ} {Γ : c.Ctx {n}} {m : _} {a : _} {A : _}
    -> (Γok : c.CtxOK Γ)
    -> Γ |- m ELAB a :->: A
    -> Γ c.|- a :: A 

elabCast->ty : {n : ℕ} {Γ : c.Ctx {n}} {m : _} {a : _} {A : _}
    -> (Γok : c.CtxOK Γ)
    -> Γ |- m ELAB a :->: A
    -> Γ c.|- A :: c.pTyU

elabCast<-ty : {n : ℕ} {Γ : c.Ctx {n}} {m : _} {A : _}
    -> (Γok : c.CtxOK Γ)
    -> Γ |- m ELAB A :<-: c.pTyU
    -> Γ c.|- A :: c.pTyU
elabCast<-ty Γok (Cast x) = c.Cast (elabCast-> Γok x) (elabCast->ty Γok x) c.TyU
elabCast<-ty Γok (Conv-* x) = elabCast-> Γok x

elabCast->ty Γok (Var v x) = Γok v _ x
elabCast->ty Γok TyU = c.TyU
elabCast->ty Γok (Ann x x₁) = elabCast<-ty Γok x
elabCast->ty Γok (Pi x x₁) = c.TyU
elabCast->ty Γok (App F Arg) = {!!}
 where
 piOk : _ c.|- c.pPi _ _ :: c.pTyU
 piOk = elabCast->ty Γok F
 -- Pi inversion   B : *, A : *
 -- by elabCast<-  Γ c.|- a :: A
 -- by subst       Γ c.|- B c.[ a ] :: c.pTyU

elabCast<- : {n : ℕ} {Γ : c.Ctx {n}} {m : _} {a : _} {A : _}
    -> (Γok : c.CtxOK Γ)
    -> (Aok : Γ c.|- A :: c.pTyU)
    -> Γ |- m ELAB a :<-: A
    -> Γ c.|- a :: A 
elabCast<- Γok Aok (Fun x) = c.Fun {!!}
 where
 -- Pi inversion   B : *, A : *
 -- incuction on x
elabCast<- Γok Aok (Cast x) = c.Cast (elabCast-> Γok x) (elabCast->ty Γok x) Aok
elabCast<- Γok Aok (Conv-* x) = c.Conv (elabCast-> Γok x) (c.refl~~ c.pTyU)


elabCast-> Γok (Var v x) = c.Var v x
elabCast-> Γok TyU = c.TyU 
elabCast-> Γok (Ann x yy) = elabCast<- Γok (elabCast<-ty Γok x) yy
elabCast-> Γok (Pi x yy) = c.Pi (elabCast<-ty Γok x) (elabCast<-ty {!!} yy) -- ok since, x : *
elabCast-> Γok (App x yy) = c.App (elabCast-> Γok x) (elabCast<- Γok {!!} yy) -- ok since, A : * by Pi inversion


CtxMappedOK : {n : ℕ} -> (Γ : pCtx {n}) -> (H : c.Ctx {n}) -> Set
CtxMappedOK Γ H = (v : _) -> (M : _ ) -> In Γ v M -> Σ _ λ A → (c.In H v A) × (H |- M ELAB A :<-: c.pTyU)
-- -> c.In H v A -> H |- M ELAB A :<-: c.pTyU

-- record

bidirElab<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  {m : _} {M : _} {A : _}
    -> (ΓHok : CtxMappedOK Γ H)
    -> Γ |- m :<-: M
    -> H |- M ELAB A :<-: c.pTyU
    -> Σ _ (λ a → (H |- m ELAB a :<-: A))
bidirElab<- ΓHok (Fun x x₁ x₂) ok = {!!}
bidirElab<- ΓHok (Conv x x₁) ok = {!!}

bidirElab-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  {m : _} {M : _} -- {a : _} {A : _}
    -> (ΓHok : CtxMappedOK Γ H)
    -> Γ |- m :->: M
--    -> H |- M ELAB a :-> A
    -> Σ _ (λ a → Σ _ (λ A → (H |- m ELAB a :->: A) × (H |- M ELAB A :<-: c.pTyU)))
bidirElab-> ΓHok (Var x v x₁) = {!!}
bidirElab-> ΓHok (TyU x) = {!!}
bidirElab-> ΓHok (Ann x x₁) = {!!}
bidirElab-> ΓHok (Pi aTy bodTy) = {!!}
bidirElab-> ΓHok (App fd ad) with bidirElab-> ΓHok fd
... | f , F , fst , snd = {!!}
-- at this point would need an inversion to say
-- H |- pPi aTy bodTy ELAB F :<-: c.pTyU implies F = c.pPi aTy' bodT', but htis is contrecticted ... :: *



bidirElab2-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  {m : _} {M : _} -- {a : _} {A : _}
    -> (ΓHok : CtxMappedOK Γ H)
    -> Γ |- m :->: M
--    -> H |- M ELAB a :-> A
    -> Σ _ (λ a → Σ _ (λ A → (H |- m ELAB a :->: A)))
bidirElab2-> ΓHok (Var x v x₁) = {!!} , ({!!} , Var v {!!}) -- ok, this works
bidirElab2-> ΓHok (TyU x) = c.pTyU , (c.pTyU , TyU)
bidirElab2-> ΓHok (Ann x xx) with bidirElab<- ΓHok x (Conv-* TyU)
... | A , Aelab with bidirElab<- ΓHok xx Aelab
... | a , aelab = a , (A , (Ann Aelab aelab))
bidirElab2-> ΓHok (Pi aTy bodTy) with bidirElab<- ΓHok aTy (Conv-* TyU)
... | A , Aelab with bidirElab<- {!!} bodTy (Conv-* TyU) -- ok
... | B , Belab = (c.pPi A B) , c.pTyU , Pi Aelab Belab
bidirElab2-> ΓHok (App fd ad) with bidirElab-> ΓHok fd
... | f , xxx = {!!}


bidirElab1<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  {m : _} {M : _}
    -> (ΓHok : CtxMappedOK Γ H)
    -> Γ |- m :<-: M
--    -> H |- M ELAB a :-> A
    -> Σ _ (λ a → Σ _ (λ A → (H |- m ELAB a :<-: A)))

bidirElab1<- ΓHok (Fun x x₁ x₂) = {!!} , ({!!} , Fun {!!})
bidirElab1<- ΓHok (Conv x x₁) = {!!} , ({!!} , Cast {!!}) -- ok this leaves some info on the table, M~A
  where
  xx = bidirElab-> ΓHok x


{-
CtxOK Γ
Γ |- m ELAB a :->: A

elabCastty-> : {!{m : _} {a : _} {A : _} {B : _}
    -> Γ |- m ELAB a :->: A!}
elabCastty-> = {!!}
ar
data _|-ELAB_ : {n : ℕ} (Γ : pCtx {n}) -> c.Ctx {n} -> Set where
  emp-ELAB : pEmp |-ELAB c.Emp
  ext-ELAB : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} {M : _}
    -> Γ |-ELAB H -> {A : _}
    -- -> H |- M ELAB A :<-: c.pTyU
    -> pExt Γ M |-ELAB c.Ext H A
-}
