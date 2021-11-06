module elab where

open import presyntax
open import bidir
open import elab

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




{-
3 options to repair this
* don't assign casts to * derivations, conv over *
* don't care that casts are assigned (reduction over Fun)
* allow casts to *, allow conv, restrict assumption somehow
-}





bi-elabs<-Elab : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :<-: M)
  -> {A AT : _}
  -> H |- M ELAB A :->: AT
  --  -> Pluas M A AT
  -> Σ _ λ a →  ( Σ _ λ A' →  H |- m ELAB a :<-: A' ) -- × Pluas m a A' × Pluas M A' AT)


bi-elabs<-ElabWeak : {n : ℕ} {Γ : pCtx {suc n}} {H : c.Ctx {n}}
  -> {W : _}
  -> (ctxElab : Γ |-ELAB  c.Ext H W)
  -> {m : _ } {M : _}
  -> (ty : Γ |- m :<-: po M)
  -> {A AT : _}
  -> c.Ext H W |- po M ELAB c.o A :->: c.o AT
  --  -> Pluas M A AT
  -> Σ _ λ a →  ( Σ _ λ A' → c.Ext H W |- m ELAB a :<-: c.o A' ) -- × Pluas m a A' × Pluas M A' AT)
bi-elabs<-ElabWeak = {!!}

bi-elabs<-Fun : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m : _} {M : _}
  -> (ty : Γ |- pFun m :<-: M)
  -> {A AT : _}
  -> H |- M ELAB A :->: AT
  --  -> Pluas M A AT
  ->  Σ _ λ A → Σ _ (λ B → Σ _ (λ b → (c.Ext (c.Ext H A) (c.o (c.pPi A B))) |- m ELAB b :<-: c.o B) )
bi-elabs<-Fun ctxElab (Fun ty ty₁ Bod) (Pi x BodTy) with bi-elabs<-ElabWeak {!!} Bod {!!} --weaken conv-* BodTy
... | fst , fst₁ , snd = {!fst!} , ( fst₁ , ({!x!} , {!snd!}))
  
bi-elabs<-Elab ctxElab f@(Fun ty ty₁ Bod) p@(Pi x BODTY) -- (PLPi xx xx₁)
  with bi-elabs<-ElabWeak {!!} Bod {!!} -- (o-elab (Conv-* BODTY))
    where
      BOdTy = Conv-* BODTY
... | xx = {!!}
{-
  with bi-elabs<-Fun ? f p
... | fst , fst₁ , fst₂ , snd = c.pFun fst₂ , ((c.pPi fst fst₁) , (Fun snd)) -}
bi-elabs<-Elab ctxElab (Conv ty _ _) x with bi-elabs-> ctxElab ty
... | fst , fst₁ , fst₂ , snd = (c.pCast fst fst₁ _) , (_ , (Cast fst₂))

--NOTFUN
{-

bi-elabs<-Elab : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :<-: M)
  -> NOTFUN m
  -> {A AT : _}
  -> H |- M ELAB A :->: AT
  -> Σ _ λ a →  ( Σ _ λ A' →  H |- m ELAB a :<-: A') -- × Pluas m a A' × Pluas M A' AT

bi-elabs-> ctxElab (Ann (Conv ty@(Pi aTy bodTy) x₁ MYT) m@(Fun _ _ _)) with bi-elabs-> ctxElab ty
... | .(c.pPi _ _) , .c.pTyU , fst₂ , PLPi snd snd₁ with bi-elabs<- ctxElab m {!c!} 
... | fst , fst₁ , snd₂ = {!!} , ({!!} , ({!!} , {!!}))
bi-elabs-> ctxElab (Ann MYT (Conv x x₁ M)) = {!!}
-}
{-
 with bi-elabs<-Ty ctxElab MYT
... | ATY , EATY , ATYok with bi-elabs<- ctxElab M {ATY} {!!}
... | xx = {!!}
bi-elabs<-Fun : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m : _} {N : _}{M : _}
  -> Γ |- m :<-: M
  ->  Σ _ λ A → Σ _ (λ B → Σ _ (λ b → (H |- pFun m ELAB c.pFun b :<-: c.pPi A B )))
bi-elabs<-Fun ctxElab  = {!!}
-}




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













record out->  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H) {m M : PreSyntax {n}} (ty : Γ |- m :->: M) : Set where
  field
    a A : c.PreSyntax {n}
    elab : H |- m ELAB a :->: A

record out<-  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H)
  (m M : PreSyntax {n})  (A : c.PreSyntax {n}) : Set where
  field
    a : c.PreSyntax {n}
    elab : H |- m ELAB a :<-: A
   -- elabTy : H |- M ELAB A :<-: c.pTyU

consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :->: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B × H |- M ELAB A :->: c.pTyU × c.Ext H A |- N ELAB B :<-: c.pTyU -- TODO arrow swap still ok?
  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :<-: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B



bi-elabs-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :->: M)
  -> out-> ctxElab ty

bi-elabs<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> Γ |- m :<-: M
  -> {A : _}
  -> H |- M ELAB A :->: c.pTyU
--  -> H |- M ~ A 
  -> out<- ctxElab m M A

bi-elabs<-TyU : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : PreSyntax {n}}
  -> Γ |- M :<-: pTyU
  -> Σ _ λ A → H |- M ELAB A :->: c.pTyU



bi-elabs<-TyU' : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M U : PreSyntax {n}}
  -> Γ |- M :<-: U -> U ~~ pTyU
  -> Σ _ λ A → H |- M ELAB A :->: c.pTyU


bi-elabs<-TyU ctxElab (Conv under red ty) = {!!}



-- pluasable
bi-elabs->TyU : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M U : PreSyntax {n}}
  -> Γ |- M :->: U -> U ~~ pTyU
  -> Σ _ λ A → H |- M ELAB A :->: c.pTyU
bi-elabs->TyU ctxElab (Var x v x₁) red = {!!} -- TODO constraint on store
bi-elabs->TyU ctxElab (TyU x) red = c.pTyU , TyU
bi-elabs->TyU ctxElab (Ann ATY A) red = {!!}
-- with bi-elabs<-TyU ctxElab ATY | bi-elabs<-TyU' ctxElab A red
--... | fst₁ , snd₁ | fst , snd = fst , ((Ann (Conv-* {!!}) (Conv-* snd)))
-- {!!} , (Ann {!!} (Conv-* snd))
bi-elabs->TyU ctxElab (Pi aTy bodTy) red = {!!} , (Pi {!!} {!!})
bi-elabs->TyU ctxElab (App ty x) red = {!!} -- either 




bi-elabs<-TyU' ctxElab (Fun ty ty₁ ty₂) ee = {!!} -- IMPOSSIBLE  by stability of constructors
bi-elabs<-TyU' ctxElab (Conv x xy ty) yz = bi-elabs->TyU ctxElab x (trans~~ xy yz)










bi-elabs-> {_} {Γ} ctxElab (Var x v lkup) with in-both ctxElab v lkup
bi-elabs-> {_} {Γ} ctxElab (Var x v lkup) | fst , fst₁ , snd
  = record { a = c.pVar v ; A = fst ; elab = Var v fst₁ }
bi-elabs-> ctxElab (TyU x) = record { a = c.pTyU ; A = c.pTyU ; elab = TyU }

bi-elabs-> ctxElab (Ann M m) with bi-elabs<-TyU ctxElab M
... | A , MA with bi-elabs<- ctxElab m MA
... | record { a = a ; elab = elab } = record { a = a ; A = A ; elab = Ann (Conv-* MA) elab }
bi-elabs-> ctxElab (Pi argTy bodTy) with bi-elabs<-TyU ctxElab argTy
... | A , Aelab with bi-elabs<-TyU  (ext-ELAB ctxElab) bodTy 
... | B , BElab = record { a = c.pPi A B ; A = c.pTyU ; elab = Pi (Conv-* Aelab) (Conv-* BElab) }
bi-elabs-> ctxElab (App F Arg) with bi-elabs-> ctxElab F
... | record { a = b ; A = B ; elab = Felab } with consistent-lemma ctxElab F Felab 
... | aty , bty , red , Aty , Bty with bi-elabs<- ctxElab Arg Aty
... | record { a = a ; elab = elab } = record { a = c.pApp b a ; A = bty c.[ a ] ; elab = App Felab red elab }



bi-elabs<- ctxElab (Fun ty BodTy Bod) (Pi x x₁) with bi-elabs<- ( ((ext-ELAB (ext-ELAB ctxElab)))) Bod {!!} --weaken BodTy
... | record { a = a ; elab = elab } = record { a = c.pFun a ; elab = Fun elab }
bi-elabs<- ctxElab (Conv ty eq e) x with bi-elabs-> ctxElab ty
... | record { a = a ; A = A ; elab = elab } = record { a = c.pCast a A _ ; elab = Cast elab }


-- bi-elabs<-TyU ctxElab (Conv under _ ty) with bi-elabs-> ctxElab under
-- ... | record { a = a ; A = A ; elab = elab } = c.pCast a A c.pTyU , Conv elab


consistent-lemma ctxElab (Var x .v x₂) (Var v x₁) = {!!} -- condition on elaborated ctxs
consistent-lemma ctxElab (Ann x x₃) (Ann x₁ x₂) = {!!} -- by consistent-lemma<-
consistent-lemma ctxElab x (App ee x₁ x₂) = {!!}
-- must be that, bodTy [ a₁ ] ≟ pPi M₁ N₁
-- thus bodTy ≟ pPi M₁' N₁' and folloews by (mutual?) induction
-- or  bodTy = x, a₁ ≟ pPi M₁ N₁ and folloews by (mutual?) induction


consistent-lemma<- ctxElab x (Fun ee) = {!!}
consistent-lemma<- ctxElab x (Cast x₁) = {!!}
consistent-lemma<- ctxElab x (Conv-* x₁) = {!!}



bi-elabs-ctx : {n : ℕ}
  -> (Γ : pCtx {n})
  -> Σ (c.Ctx {n}) λ H → Γ |-ELAB H
bi-elabs-ctx = {!!} -- bidierctional reg







-- TODO if regularity is required make changes to chapter 2



































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
    
  App : {m n : _} {b a : _} {C A : _} {B : _}
    -> Γ |- m ELAB b :->: C
    -> C c~>p* c.pPi A B
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


data _|-ELAB_ : {n : ℕ} (Γ : pCtx {n}) -> c.Ctx {n} -> Set where
  emp-ELAB : pEmp |-ELAB c.Emp
  ext-ELAB : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} {M : _}
    -> Γ |-ELAB H -> {A : _}
    -- -> H |- M ELAB A :<-: c.pTyU
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
  ->  H c.|- A :: c.pTyU
  -> (H |- m ELAB a :<-: A)
  -> c._|-_::_ H a A




reg-> ok (Var v x) = ok v _ x
reg-> ok TyU = c.TyU
reg-> ok (Ann x _) = {!!}
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


reg<- ok (Cast x) = c.Cast (well-cast-> ok x) (reg-> ok x) c.TyU    


-- TODO without ok or c.reg? don't think this is possible
well-cast<- {_} {H} ok ty (Fun {m } {b} {A} {B} e) = c.Fun (well-cast<- {!!} BTy' e) -- by ext wf
  where
    BTy : c.Ext H A c.|- B :: c.pTyU
    BTy = {!!} -- pi inversion on ty

    BTy' : c.Ext (c.Ext H A) (c.o (c.pPi A B)) c.|- c.o B :: c.pTyU
    BTy' = {!!} -- weaken


well-cast<- ok ty (Cast e) = c.Cast (well-cast-> ok e) (reg-> ok e) ty

well-cast-> ok (Var v x) = c.Var v x
well-cast-> ok TyU = c.TyU
well-cast-> ok (Ann ty bod) = {!!} -- well-cast<- ok (well-cast<- ok c.TyU ty) bod
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

postulate
  in-both : {n : ℕ}{Γ : pCtx {n}} {H : c.Ctx {n}} 
    -> Γ |-ELAB H
    -> (v : Fin n)
    -> {M : PreSyntax {n}}
    -> In Γ v M
    -> Σ (c.PreSyntax {n}) λ A → c.In H v A × H |- M ELAB A :<-: c.pTyU
 



record out->  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H) {m M : PreSyntax {n}} (ty : Γ |- m :->: M) : Set where
  field
    a A : c.PreSyntax {n}
    elab : H |- m ELAB a :->: A

record out<-  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H)
  (m M : PreSyntax {n})  (A : c.PreSyntax {n}) : Set where
  field
    a : c.PreSyntax {n}
    elab : H |- m ELAB a :<-: A
   -- elabTy : H |- M ELAB A :<-: c.pTyU

consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :->: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B × H |- M ELAB A :<-: c.pTyU × c.Ext H A |- N ELAB B :<-: c.pTyU -- TODO arrow swap still ok?
  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :<-: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B

consistent-lemma = {!!}
consistent-lemma<- = {!!}



bi-elabs-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :->: M)
  -> out-> ctxElab ty

bi-elabs<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> Γ |- m :<-: M
  -> {A : _}
  -> H |- M ELAB A :->: c.pTyU
--  -> H |- M ~ A 
  -> out<- ctxElab m M A

bi-elabs<-TyU : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : PreSyntax {n}}
  -> Γ |- M :<-: pTyU
  -> Σ _ λ A → H |- M ELAB A :<-: c.pTyU


bi-elabs->TyU : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : PreSyntax {n}}
  -> Γ |- M :->: pTyU
  -> Σ _ λ A → H |- M ELAB A :->: c.pTyU

bi-elabs-> {_} {Γ} ctxElab (Var x v lkup) with in-both ctxElab v lkup
bi-elabs-> {_} {Γ} ctxElab (Var x v lkup) | fst , fst₁ , snd
  = record { a = c.pVar v ; A = fst ; elab = Var v fst₁ }
bi-elabs-> ctxElab (TyU x) = record { a = c.pTyU ; A = c.pTyU ; elab = TyU }

bi-elabs-> ctxElab (Ann _ m) with swapzies<- m
... | M , e:<-:M , M:->:Ty with bi-elabs->TyU ctxElab  M:->:Ty 
... | A , M~A with bi-elabs<- ctxElab e:<-:M M~A
... | record { a = a ; elab = elab } = record { a = {!!} ; A = {!!} ; elab = {!!}}
{-
-- swapzies<-
bi-elabs-> ctxElab (Ann M m) with bi-elabs->TyU ctxElab {!!} -- M
... | fst , snd with bi-elabs<- ctxElab m snd
... | record { a = a ; elab = elab } = record { a = a ; A = fst ; elab = Ann {!!} elab }
-}
bi-elabs-> ctxElab (Pi argTy bodTy) with bi-elabs<-TyU ctxElab argTy
... | A , Aelab with bi-elabs<-TyU  (ext-ELAB ctxElab) bodTy 
... | B , BElab = record { a = c.pPi A B ; A = c.pTyU ; elab = Pi Aelab BElab }
bi-elabs-> ctxElab (App F Arg) with bi-elabs-> ctxElab F
... | record { a = b ; A = B ; elab = Felab } with consistent-lemma ctxElab F Felab 
... | aty , bty , red , Aty , Bty with bi-elabs<- ctxElab Arg {!!}
... | record { a = a ; elab = elab } = record { a = c.pApp b a ; A = bty c.[ a ] ; elab = App Felab red elab }



bi-elabs<- ctxElab (Fun ty BodTy Bod) (Pi x x₁) with bi-elabs<- ( ((ext-ELAB (ext-ELAB ctxElab)))) Bod {!!} --weaken BodTy
... | record { a = a ; elab = elab } = record { a = c.pFun a ; elab = Fun elab }
bi-elabs<- ctxElab (Conv ty eq e) x with bi-elabs-> ctxElab ty
... | record { a = a ; A = A ; elab = elab } = record { a = c.pCast a A _ ; elab = Cast elab }

bi-elabs->TyU ctxElab x = {!!}
{-
with bodTy [ a ]
... | x
-}

bi-elabs<-TyU = {!!}
-- bi-elabs<-TyU ctxElab (Conv under _ ty) with bi-elabs-> ctxElab under
-- ... | record { a = a ; A = A ; elab = elab } = c.pCast a A c.pTyU , Conv elab




bi-elabs-ctx : {n : ℕ}
  -> (Γ : pCtx {n})
  -> Σ (c.Ctx {n}) λ H → Γ |-ELAB H
bi-elabs-ctx = {!!} -- bidierctional reg







-- TODO if regularity is required make changes to chapter 2


























{-



data _|-_ELAB_:->:_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set
data _|-_ELAB_:<-:_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set
data _|-_ELAB-Ty_ {n : ℕ} (Γ : c.Ctx {n}) : PreSyntax {n} -> c.PreSyntax {n} -> Set

postulate
  _c~>p*_ :  {n : ℕ} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set

  o-> : {n : ℕ} {m : _} {a : _} {aTy : _} {ty : _} {Γ : c.Ctx {n}} -> Γ |- m ELAB a :->: aTy
    -> c.Ext Γ ty |- po m ELAB c.o a :->: c.o aTy
    {-
  o-== : {n : ℕ} {a a' aTy ty : PreSyntax {n}} {Γ : Ctx} -> Γ |- a == a' :: aTy -> {Ty : Γ |- ty :: pTyU}
    -> Ext Γ Ty |- po a == po a' :: po aTy
-}


data _|-_ELAB-Ty_ {n} Γ  where
  TyU : Γ |- pTyU ELAB-Ty c.pTyU
  
  Pi : {M : _} {N : _} {A : _} {B : _}
    -> Γ |- M ELAB A :<-: c.pTyU
    -> c.Ext Γ A |- N ELAB B :<-: c.pTyU
    -> Γ |- (pPi M N) ELAB-Ty (c.pPi A B)
    

data _|-_ELAB_:->:_ {n} Γ  where
  Var : -- TODO could index 2 ctxs?
    (v : Fin n) -> {ty : _} -> c.In Γ v ty
    -> Γ |- (pVar v) ELAB (c.pVar v) :->: ty
  Ann : {m M : _} {a A : c.PreSyntax }
    -> Γ |- M ELAB-Ty A
    -> Γ |- m ELAB a :<-: A
    -> Γ |- (pAnn m M) ELAB a :->: A
    
  App : {m n : _} {b a : _} {C A : _} {B : _}
    -> Γ |- m ELAB b :->: C
    -> C c~>p* c.pPi A B
    -> Γ |- n ELAB a :<-: A
    -> Γ |- (pApp m n) ELAB (c.pApp b a) :->: (B c.[ a ])
    
  ty-> : {M : _} {A : c.PreSyntax }
    -> Γ |- M ELAB-Ty A 
    -> Γ |- M ELAB A :->: c.pTyU
    
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


data _|-ELAB_ : {n : ℕ} (Γ : pCtx {n}) -> c.Ctx {n} -> Set where
  emp-ELAB : pEmp |-ELAB c.Emp
  ext-ELAB : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} {M : _}
    -> Γ |-ELAB H -> {A : _}
    -- -> H |- M ELAB A :<-: c.pTyU
    -> pExt Γ M |-ELAB c.Ext H A




preserv-pi : {n : ℕ} {H : c.Ctx {n}} {H: }
  -> H |- pPi aty bodty ELAB A :<-: c.pTyU

data _|-_~_ {n : ℕ} (Γ : c.Ctx {n}) (m : PreSyntax {n}) (a : c.PreSyntax {n}) : Set where
  inf : {c : _} -> Γ |- m ELAB a :->: c -> Γ |- m ~ a
  ch : {c : _} -> Γ |- m ELAB a :<-: c -> Γ |- m ~ a
-}


-- elaboration from bi has == conversions?
-- if |- M : * and M Elab C and if M ~>* (A -> B) then C ~>* (A' -> B')

--  ×
{-
consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :->: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B
  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :<-: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B


consistent-lemma ctxElab (Var x .v x₂) (Var v x₁) = {!!}  {!!} , ({!!} , {!!}) -- by erasure of the lookup ctxElab
consistent-lemma ctxElab (Ann x x₃) (Ann x₁ x₂) = consistent-lemma<- ctxElab x₃  x₂
consistent-lemma ctxElab x (App e x₁ x₂) = {!!}
-- must be that, bodTy [ a₁ ] ≟ pPi M₁ N₁
-- thus bodTy ≟ pPi M₁' N₁' and folloews by (mutual?) induction
-- or  bodTy = x, a₁ ≟ pPi M₁ N₁ and folloews by (mutual?) induction

consistent-lemma<- ctxElab (Fun x x₁ x₂) (Fun e) = {!!} -- directly
consistent-lemma<- ctxElab (Conv x x₂ x₃) (Conv x₁) = {!!}
 --by def of ==, , induction on sub-der

-- elaborates up to conversion
_|-_ELAB_:~>:_ : {n : ℕ} (Γ : c.Ctx {n}) -> PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set
Γ |- m ELAB a :~>: aty = Σ _ λ aty' → ( Γ |- m ELAB a :->: aty') × (aty' c.~~ aty) 
-}






{-
bidirection elabs

well-cast<- (Fun argTy bodTy bod) --  MTy
  with well-cast<- bod  --| well-cast<- argTy | well-cast<- bodTy | 
... | fst , fst₁ , fst₂ , fst₃ , bodElab = {!!} , ({!!} , ({!!} , ({!!} , (Fun {!!}))))
well-cast<- (Conv x x₁ mTy) -- MTy
  = {!!}

well-cast-> = {!!}
-}

{-
bi-elabs<- ctxElab (Fun e e₁ Bod) (Pi _ _) with bi-elabs<- ((ext-ELAB (ext-ELAB ctxElab))) Bod {!!}
... | record { a = a ; elab = elab } = record { a = c.pFun a ; elab = Fun elab }
bi-elabs<- ctxElab (Conv ty eq e) x with bi-elabs-> ctxElab ty
... | record { a = a ; A = A ; elab = elab } = record { a = c.pCast a A _ ; elab = Cast elab }
-- = record { a = {!!} ; elab = Cast {!!} }
{-
bi-elabs<- ctxElab x (Cast x₁) with bi-elabs<- ctxElab x {!!}
... | record { a = a ; elab = elab } = record { a = {!!} ; elab = Cast {!!} }

bi-elabs<- ctxElab (Fun aTy bTy Bod) (Cast {_} {ppi} pi@(Pi {M} {N} {A} {B} aTy' bTy')) with bi-elabs<-TyU (ext-ELAB ctxElab {A}) bTy -- with bi-elabs<- ((ext-ELAB (ext-ELAB ctxElab))) Bod {!!} -- (ext-ELAB (ext-ELAB ctxElab)) (conv (o-> pi))) Bod {!o->!}
... | fst , snd  with bi-elabs<- ((ext-ELAB (ext-ELAB ctxElab {A}) {c.o ppi})) Bod w
    where -- pExt Γ aty |- bodty :<-: pTyU
    w : {x : _} ->   c.Ext (c.Ext _ _) x |- po N ELAB c.o B :<-: c.pTyU --  c.Ext (c.Ext H A) x |- N ELAB B :<-: c.pTyU
    w = {!!}
... | record { a = a ; elab = elab } = record { a = {!!} ; elab = {!!} }

{-
with bi-elabs<-TyU ctxElab aTy
... | a , aTy' with bi-elabs<-TyU (ext-ELAB ctxElab aTy') bTy
... | b , bTy' with  bi-elabs<- (ext-ELAB (ext-ELAB ctxElab aTy') {!!}) Bod {!!} -- build out of  Conv (Pi aTy' ... weaken ty
... | record { a = bb ; elab = elabb ; elabTy = elabTyb } = record { a = {!!} ; elab = {!Fun!} ; elabTy = {!!} }
-}
-- 
-- with bi-elabs<- {!!} Bod {!!}
-- ... | xx = {!!}
bi-elabs<- ctxElab (Conv x x₁ b) e = {!!}
-- record { a = c.pFun {!!} ; A = {!c.Pi!} ; elab = Fun {!!} ; elabTy = {!Pi!} }
--bi-elabs<- ctxElab (Conv under _ ty) with bi-elabs-> ctxElab under | bi-elabs<-TyU ctxElab ty
--... | record { a = a ; A = A ; elab = elab } | fst , snd = record { a = c.pCast a A fst ; A = fst ; elab = Conv elab ; elabTy = snd }
-- suspends allmost all evaluation
-}

data _Erase_ {n : ℕ} : (PreSyntax {n}) -> c.PreSyntax {n} -> Set where

  eVar : (i : Fin n) -> (pVar i) Erase (c.pVar i)
  eTyU :  pTyU Erase c.pTyU
  -- ePi :  (aTy : PreSyntax {n}) -> (bodTy :  PreSyntax {suc n}) -> PreSyntax
  --eFun : (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  --eApp :  (f : PreSyntax {n}) -> (a : PreSyntax {n}) -> PreSyntax
  --eAnn :  (e : PreSyntax {n}) -> (ty : PreSyntax {n}) -> PreSyntax
  --eCast


-- elaboration from bi has == conversions?
-- if |- M : * and M Elab C and if M ~>* (A -> B) then C ~>* (A' -> B')

--  ×
{-
consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :->: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B
  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :<-: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B


consistent-lemma ctxElab (Var x .v x₂) (Var v x₁) = {!!}  {!!} , ({!!} , {!!}) -- by erasure of the lookup ctxElab
consistent-lemma ctxElab (Ann x x₃) (Ann x₁ x₂) = consistent-lemma<- ctxElab x₃  x₂
consistent-lemma ctxElab x (App e x₁ x₂) = {!!}
-- must be that, bodTy [ a₁ ] ≟ pPi M₁ N₁
-- thus bodTy ≟ pPi M₁' N₁' and folloews by (mutual?) induction
-- or  bodTy = x, a₁ ≟ pPi M₁ N₁ and folloews by (mutual?) induction

consistent-lemma<- ctxElab (Fun x x₁ x₂) (Fun e) = {!!} -- directly
consistent-lemma<- ctxElab (Conv x x₂ x₃) (Conv x₁) = {!!}
 --by def of ==, , induction on sub-der-

-- elaborates up to conversion
_|-_ELAB_:~>:_ : {n : ℕ} (Γ : c.Ctx {n}) -> PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set
Γ |- m ELAB a :~>: aty = Σ _ λ aty' → ( Γ |- m ELAB a :->: aty') × (aty' c.~~ aty) 
-}
{-
data _|-_~_ {n : ℕ} (Γ : c.Ctx {n}) (m : PreSyntax {n}) (a : c.PreSyntax {n}) : Set where
  inf : {c : _} -> Γ |- m ELAB a :->: c -> Γ |- m ~ a
  ch : {c : _} -> Γ |- m ELAB a :<-: c -> Γ |- m ~ a
-}