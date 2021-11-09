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
 

  o-elab-> :  {n : ℕ}{H : c.Ctx {n}} {m : _} {a : _} {A : _}
    -> H |- m ELAB a :->: A
    -> {W : _}
    -> c.Ext H W |- po m ELAB c.o a :->: c.o A

  o-elab<- :  {n : ℕ}{H : c.Ctx {n}} {m : _} {a : _} {A : _}
    -> H |- m ELAB a :<-: A
    -> {W : _}
    -> c.Ext H W |- po m ELAB c.o a :<-: c.o A

data Opts {n : ℕ} {Γ : pCtx {n}} : Set where
  isFun : Opts

which : {n : ℕ} {Γ : pCtx {n}} 
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :<-: M)
  -> Opts {n} {Γ}
which (Fun ty ty₁ ty₂) = {!!}
which (Conv x x₁ ty) = {!!}

data Pluas {n : ℕ} : PreSyntax {n} -> c.PreSyntax {n} -> c.PreSyntax {n} -> Set where
  PlFun : {N : _} {b : _} {B : _}
    -> Pluas N b (c.o B)
    -> {A : _}
    -> Pluas (pFun N) (c.pFun b) (c.pPi A B)
    
  PLVar : {i : _} {a  : _}{A : _} -> Pluas (pVar i) a A -- TODO might get cast
  PLTyU :  Pluas (pTyU) c.pTyU (c.pTyU)
  PLANN : {N : _} {M : _} {a : _} 
    -> {A : _}
    -> Pluas (pAnn N M) a A
  PLPi : {N : _} {M : _} {A : _} {B : _}
    -> Pluas N  A c.pTyU
    -> Pluas M  B c.pTyU
    -> Pluas (pPi N M)  (c.pPi A B) c.pTyU
   
  PLApp : {N : _} {M : _} {a : _} 
    -> {A : _}
    -> Pluas (pApp N M) a A



data Pluas<- {n : ℕ} : PreSyntax {n} -> c.PreSyntax {n} -> Set where
  PlFun<- : {N : _} {B : _}
    -> Pluas<- N (c.o B)
    -> {A : _}
    -> Pluas<- (pFun N) (c.pPi A B)
    
  PLVar<- : {i : _} {A : _} -> Pluas<- (pVar i) A
  PLTyU<- : Pluas<- (pTyU) c.pTyU
  PLANN<- : {N : _} {M : _}
    -> {A : _}
    -> Pluas<- (pAnn N M) A
  PLPi<- : {N : _} {M : _}
    -> Pluas<- N c.pTyU
    -> Pluas<- M c.pTyU
    -> Pluas<- (pPi N M) c.pTyU
   
  PLApp<- : {N : _} {M : _}
    -> {A : _}
    -> Pluas<- (pApp N M) A



data NOTFUN {n : ℕ} :  PreSyntax {n} -> Set where
  PLVar<- : {i : _} -> NOTFUN (pVar i)
  PLTyU<- :  NOTFUN pTyU
  PLANN<- : {N : _} {M : _}
    -> NOTFUN (pAnn N M)
  PLPi<- : {N : _} {M : _}
    -> NOTFUN (pPi N M)
  PLApp<- : {N : _} {M : _}
    -> NOTFUN (pApp N M)


plausTy : {n : ℕ} {M : _} {A : _} -> Pluas {n} M A c.pTyU ->  {e : _} -> Pluas<- e A
plausTy PLVar = {!!}
plausTy PLTyU = {!!}
plausTy PLANN = {!!}
plausTy (PLPi x x₁) = {!!}
plausTy PLApp = {!!}

bi-elabs-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :->: M)
  -> Σ _ λ a →  Σ _ λ A → H |- m ELAB a :->: A × Pluas m a A



bi-elabs<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :<-: M)
  -> {A : _}
  -> Pluas<- m A
  -> Σ _ λ a →  H |- m ELAB a :<-: A × Pluas m a A

--For real would need to quantify over all depths of weakening
bi-elabs<-FunWeak : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : PreSyntax }
  -> Γ |-  M :<-: pTyU
  -> {W : _}
  -> {m : PreSyntax } -> pExt Γ W |- m :<-: po M
  -> Σ _ λ a → Σ _ λ A →
     H |- M ELAB A :<-: c.pTyU × 
     (( B : _) →  c.Ext H B |- m ELAB a :<-: c.o A)

bi-elabs<-Fun : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : PreSyntax }
  -> Γ |-  M :<-: pTyU
  -> {m : PreSyntax } -> Γ |- m :<-: M
  -> Σ _ λ a → Σ _ λ A →
     H |- M ELAB A :<-: c.pTyU × 
     H |- m ELAB a :<-: A


bi-elabs<-Ty : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m : PreSyntax {n}}
  -> (ty : Γ |- m :<-: pTyU)
  -> Σ _ λ a →  H |- m ELAB a :<-: c.pTyU × Pluas m a c.pTyU

bi-elabs-> ctxElab (Var x v x₁) = {!!}
bi-elabs-> ctxElab (TyU x) = c.pTyU , c.pTyU , TyU , PLTyU
bi-elabs-> ctxElab (Pi aTy bodTy)  with bi-elabs<-Ty ctxElab aTy
... | A , EA , AOK with bi-elabs<-Ty {!!} bodTy
... | B , EB , BOK = c.pPi A B , (c.pTyU , ((Pi EA EB) , PLPi AOK BOK))

bi-elabs-> ctxElab (Ann ty m) with bi-elabs<-Fun ctxElab ty m
... | fst , fst₁ , fst₂ , snd = fst , (fst₁ , ((Ann fst₂ snd) , PLANN))

bi-elabs-> ctxElab (App ty x) with bi-elabs-> ctxElab ty
... | fst , fst₁ , fst₂ , snd = {!!}


  
consistent-lemma<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}  -- might be wrong IH
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :<-: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :<-: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B

consistent-lemma : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _} {N : _}
  -> {m : PreSyntax {n}}
  -> Γ |- m :->: pPi M N
  -> {c C : _}
  -> H |- m ELAB c :->: C
  -> Σ _ λ A →  Σ _ λ B → C c~>p* c.pPi A B
consistent-lemma ctxElab (Var x .v x₂) (Var v x₁) = {!!} -- from ctx
consistent-lemma ctxElab (Ann x x₃) (Ann x₁ x₂) = {!!}  -- by induction + trans
consistent-lemma ctxElab x (App yy x₁ x₂) = {!!}
-- must be that, bodTy [ a₁ ] ≟ pPi M₁ N₁
-- thus bodTy ≟ pPi M₁' N₁' and folloews by (mutual?) induction
-- or  bodTy = x, a₁ ≟ pPi M₁ N₁ and folloews by (mutual?) induction

consistent-lemma<- ctxElab (Fun x x₁ x₂) (Fun yy) = {!!} --refl
consistent-lemma<- ctxElab (Conv x x₁ x₂) (Cast x₃) = {!!} -- by induction + trans
consistent-lemma<- ctxElab (Conv x x₁ x₂) (Conv-* x₃) = {!!} -- IMPOSSIBLE by stability

bi-elabs<-Fun ctxElab (Conv (Pi aTy bodTy) x₁ MTY) (Fun M M₁ BOD) with bi-elabs<-Ty ctxElab aTy
... | xx , yy  , zz  with bi-elabs<-FunWeak {!!} (bodTy)  BOD -- (o-elab<- fst₁)
... | fst , fst₁ , fst₂ , snd = c.pFun fst , (c.pPi xx fst₁ , (Conv-* (Pi yy fst₂) , (Fun (snd (c.oo (c.pPi xx fst₁))))))
bi-elabs<-Fun ctxElab MTY (Conv x x₁ M) with bi-elabs<-Ty ctxElab MTY | bi-elabs-> ctxElab x
... | fst , fst₁ , snd | fst₂ , fst₃ , fst₄ , snd₁ = c.pCast fst₂ fst₃ fst , (fst , (fst₁ , Cast fst₄))
  
bi-elabs<-FunWeak = {!!}




bi-elabs<- ctxElab (Fun ty ty₁ Bod) (PlFun<- x) with bi-elabs<- {!!} Bod x -- Ext!
... | b , Bod' , ok =  c.pFun b , (Fun Bod' , PlFun ok)
bi-elabs<- ctxElab (Conv (TyU x) red _) PLTyU<- = c.pTyU , ((Conv-* TyU) , PLTyU)
bi-elabs<- ctxElab (Conv (Pi aTy bodTy) red _) (PLPi<- aok bok) with bi-elabs<- ctxElab aTy aok
... | A , EA , AOK with bi-elabs<- {!!} bodTy bok
... | B , EB , BOK = c.pPi A B , ((Conv-* (Pi EA EB)) , PLPi AOK BOK)
bi-elabs<- ctxElab (Conv ty@(Ann x x₁) red _) PLANN<- with bi-elabs-> ctxElab ty
... | fst , fst₁ , TY , snd = c.pCast fst fst₁ _ , ((Cast TY) , PLANN)
bi-elabs<- ctxElab (Conv ty@(App _ x) red _) PLApp<- with bi-elabs-> ctxElab ty
... | fst , fst₁ , TY , snd = c.pCast fst fst₁ _ , ((Cast TY) , PLApp)
bi-elabs<- ctxElab (Conv ty@(Var x _ x₁) red _) PLVar<- with bi-elabs-> ctxElab ty
... | fst , fst₁ , TY , snd = c.pCast fst fst₁ _ , ((Cast TY) , PLVar)

bi-elabs<-Ty ctxElab (Conv (TyU x) x₁ ty) = c.pTyU , ((Conv-* TyU) , PLTyU)
bi-elabs<-Ty ctxElab (Conv (Pi aTy bodTy) x₁ ty) with bi-elabs<-Ty ctxElab aTy
... | A , EA , AOK with bi-elabs<-Ty {!!} bodTy
... | B , EB , BOK = c.pPi A B , ((Conv-* (Pi EA EB)) , PLPi AOK BOK)
bi-elabs<-Ty ctxElab (Conv ty@(Var x v x₂) x₁ _) with bi-elabs-> ctxElab ty
... | fst , fst₁ , TY , snd = c.pCast fst fst₁ _ , ((Cast TY) , PLVar)
bi-elabs<-Ty ctxElab (Conv ty@(Ann x x₂) x₁ _) with bi-elabs-> ctxElab ty
... | fst , fst₁ , TY , snd = c.pCast fst fst₁ _ , ((Cast TY) , PLANN)
bi-elabs<-Ty ctxElab (Conv ty@(App x x₂) x₁ _) with bi-elabs-> ctxElab ty
... | fst , fst₁ , TY , snd = c.pCast fst fst₁ _ , ((Cast TY) , PLApp)
{-
 with bi-elabs-> ctxElab ty
... | .(c.pVar _) , A , EA , PLVar = {!!}
... | .c.pTyU , .c.pTyU , TyU , PLTyU = {!!} , ({!!} , {!!})
-- {!!} , ({!!} , {!!})
... | a , A , EA , PLANN = {!!}
... | .(c.pPi _ _) , .c.pTyU , EA , PLPi = {!!}
... | a , A , EA , PLApp = {!!}






record out->  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H) (m M : PreSyntax {n}) : Set where
  field
    a A : c.PreSyntax {n}
    elab : H |- m ELAB a :->: A

record out<-  {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}} (ctxElab : Γ |-ELAB H)
  (m M : PreSyntax {n}) : Set where
  field
    a A : c.PreSyntax {n}
    elab : H |- m ELAB a :<-: A
   -- elabTy : H |- M ELAB A :<-: c.pTyU


bi-elabs-> : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> (ty : Γ |- m :->: M)
  -> out-> ctxElab m M

bi-elabs<- : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m M : PreSyntax {n}}
  -> Γ |- m :<-: M
  -> {A : _}
  -> Pluas m A
  ->  Σ _ λ a → H |- m ELAB a :<-: A


bi-elabs<-Ty : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {M : _}
  -> Γ |- M :<-: pTyU
  ->  Σ _ λ A → (H |- M ELAB A :<-: c.pTyU)

bi-elabs->Pi : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {N : _}{M : _}
  -> Γ |- pPi N M :->: pTyU
  ->  Σ _ λ A → Σ _ (λ B →  (H |- pPi N M ELAB c.pPi A B :->: c.pTyU) )


bi-elabs<-Fun : {n : ℕ} {Γ : pCtx {n}} {H : c.Ctx {n}}
  -> (ctxElab : Γ |-ELAB H)
  -> {m : _} {N : _}{M : _}
  -> Γ |- pFun m :<-: pPi N M
  ->  Σ _ λ A → Σ _ (λ B → Σ _ (λ b → (c.Ext (c.Ext H A) (c.o (c.pPi A B))) |- m ELAB b :<-: c.o B) × (H |- pPi N M ELAB c.pPi A B :<-: c.pTyU) ×  )
  -- Γ |- pFun bod :<-: pPi aty bodty
-- ((c.Ext H A) (c.o (c.pPi A B)))
-- H |- pPi N M ELAB c.pPi A B :<-: c.pTyU
{-
bi-elabs<-Fun ctxElab {pVar i} m@(Fun N M {pi} {.(pVar i)} Bod) = {!!} , ({!!} , ({!!} , (Conv-* (Pi {!!} {!!}))))
bi-elabs<-Fun ctxElab {pTyU} m@(Fun N M {pi} {.pTyU} Bod) = {!!}
bi-elabs<-Fun ctxElab {pPi bod bod₁} m@(Fun N M {pi} {.(pPi bod bod₁)} Bod) = {!!}
bi-elabs<-Fun ctxElab {pFun bod} m@(Fun N M {pi} {.(pFun bod)} Bod) = {!!}
bi-elabs<-Fun ctxElab {pApp bod bod₁} m@(Fun N M {pi} {.(pApp bod bod₁)} Bod) = {!!}
bi-elabs<-Fun ctxElab {pAnn bod bod₁} m@(Fun N M {pi} {.(pAnn bod bod₁)} Bod) = {!!}
--with bi-elabs->Pi ctxElab pi
--... | A , B , PPPi = {!!}
--with bi-elabs<- {!!} {!!} {!!}
--... | xx = {!!}
--bi-elabs<-Fun ctxElab (Fun {n} N {m} M {bod} Bod) = {!!}
--with bi-elabs->Pi {!ctxElab!} (Pi N M)
--... | A , B , snd = A , (B , ({!!} , Conv-* snd))
--with {!!} | bi-elabs->Pi {!ctxElab!} (Pi A B)
--... | xx | fst , yy = {!!}
-}

-- "not a fun"
bi-elabs<-Ty ctxElab ty@(Conv (Var x v x₃) x₁ x₂) = bi-elabs<- ctxElab ty PLVar
bi-elabs<-Ty ctxElab ty@(Conv (TyU x) x₁ x₂) =  bi-elabs<- ctxElab ty PLTyU
bi-elabs<-Ty ctxElab ty@(Conv (Ann x x₃) x₁ x₂) =  bi-elabs<- ctxElab ty PLANN
bi-elabs<-Ty ctxElab ty@(Conv (Pi aTy bodTy) x₁ x₂) =  bi-elabs<- ctxElab ty PLPi
bi-elabs<-Ty ctxElab ty@(Conv (App x x₃) x₁ x₂) =  bi-elabs<- ctxElab ty PLApp

bi-elabs->Ty = {!!}

bi-elabs->Pi ctxElab (Pi aTy bodTy) = {!!}

bi-elabs-> ctxElab (Var x v x₁) = {!!}
bi-elabs-> ctxElab (TyU x) = record { a = c.pTyU ; A = c.pTyU ; elab = TyU }
bi-elabs-> ctxElab (Pi aTy bodTy) with  bi-elabs<-Ty ctxElab aTy
... | fst , snd  with bi-elabs<-Ty {!!} bodTy -- TODO Ext.
... | ddd , ggg = record { a = c.pPi fst ddd ; A = c.pTyU ; elab = Pi snd ggg }
bi-elabs-> ctxElab (Ann (Conv (Pi aTy bodTy) red _) fTy@(Fun ee ee₁ Bod)) with bi-elabs<-Fun ctxElab fTy 
... | A , B , (b , fty) , pity = record { a = c.pFun b ; A = c.pPi A B ; elab = Ann pity (Fun fty) }
bi-elabs-> ctxElab (Ann Tyty (Conv ty red ee)) with  bi-elabs-> ctxElab ty | bi-elabs<-Ty ctxElab ee
... | record { a = a ; A = A ; elab = elab } | AA , AADer = record { a = c.pCast a A AA ; A = AA ; elab = Ann AADer (Cast elab) }
bi-elabs-> ctxElab (App ty x) = {!!}


bi-elabs<- ctxElab (Fun x x₁ Bod) (PlFun yy) with bi-elabs<- {!!}  Bod yy
... | fst , snd = (c.pFun fst) , (Fun snd)
-- ...otherwise TODO can all be cast?
bi-elabs<- ctxElab (Conv x x₁ x₂) PLVar = {!!}
bi-elabs<- ctxElab (Conv (TyU x) x₁ x₂) PLTyU = c.pCast c.pTyU c.pTyU c.pTyU , Cast TyU
bi-elabs<- ctxElab (Conv (Pi aTy bodTy) x₁ x₂) PLPi = {!!}
bi-elabs<- ctxElab (Conv x x₁ x₂) PLANN = {!!}
bi-elabs<- ctxElab (Conv x x₁ x₂) PLApp = {!!}

-- TODO if regularity is required make changes to chapter 2
-}
