module sketch where

open import Data.Nat
open import Data.Fin hiding (_+_)
-- open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])


data PreSyntax {n : ℕ} : Set
data PreSyntax {n} where
  pVar : (i : Fin n) -> PreSyntax
  pTyU : PreSyntax
  pPi :  (aTy : PreSyntax {n}) -> (bodTy :  PreSyntax {suc n}) -> PreSyntax
  pFun : (bod : PreSyntax {suc (suc n)}) -> PreSyntax
  pApp :  (f : PreSyntax {n}) -> (a : PreSyntax {n}) -> PreSyntax
  pAnn :  (e : PreSyntax {n}) -> (ty : PreSyntax {n}) -> PreSyntax


postulate
  extPreSyntax : {i j : ℕ}
    -> (ρ : (Fin i -> Fin j))
    -> Fin (suc i) -> (Fin (suc j))
 
renamePreSyntax : {i j : ℕ}
  -> (ρ : (Fin i -> Fin j))
  -> (PreSyntax {i} -> PreSyntax {j})
renamePreSyntax ρ (pVar i) = pVar (ρ i)
renamePreSyntax ρ pTyU = pTyU
renamePreSyntax ρ (pPi aTy bodTy) = pPi (renamePreSyntax ρ aTy) (renamePreSyntax (extPreSyntax ρ) bodTy)
renamePreSyntax ρ (pFun bod)
  = pFun ((renamePreSyntax (extPreSyntax (extPreSyntax ρ)) bod))
renamePreSyntax ρ (pApp f a) = pApp (renamePreSyntax ρ f) (renamePreSyntax ρ a)
renamePreSyntax ρ (pAnn e ty) = pAnn (renamePreSyntax ρ e) (renamePreSyntax ρ ty)

o : {n : ℕ} -> PreSyntax {n} -> PreSyntax {suc n}
o = renamePreSyntax (raise 1)

postulate
  substPreSyntax : ∀ {i j}
    → (σ : (Fin i → PreSyntax {j} ))
    → (PreSyntax {i}  → PreSyntax {j})


_[_] :{n : ℕ} -> PreSyntax {suc n} -> PreSyntax {n} -> PreSyntax {n}
_[_] {n} inthis withThis = substPreSyntax {suc n} {n} σ inthis
  where
    σ : Fin (suc n) → PreSyntax {n}
    σ 0F = withThis
    σ (suc x) = pVar x


data PreCtx : ℕ -> Set where
  pEmp : PreCtx 0
  _,,_ : {n : ℕ} -> PreCtx n -> PreSyntax {n} -> PreCtx (suc n)


postulate
  Ctx  : ℕ -> Set -- assume ctxs were well formed by consnstruction
  Emp : Ctx 0
  extCtx : {n : ℕ} -> Ctx n -> PreSyntax {n} -> Ctx (suc n)
  lookup : {n : ℕ} (Γ : Ctx n) -> (i : Fin n)  -> PreSyntax {n}
  _[_::=_] :{n : ℕ} -> PreSyntax {suc n} -> (i : Fin n) -> PreSyntax {n} -> PreSyntax {n}
  
  -- TODO and wll typed variants

-- system

    
data _~>p_ {n : ℕ} : PreSyntax {n}  -> PreSyntax {n} -> Set  where
  par-red : {a a' : _} -> {bod bod' : _ }
    -> (a-a' : a ~>p a')
    -> (bod-bod' : bod ~>p bod')
    -> (pApp (pFun bod)  a) ~>p ( bod' [ o (pFun bod') ] [ a' ]  )

  par-cast-red : {e e' : PreSyntax} -> {ty : PreSyntax}
    ->  e ~>p e' 
    -> (pAnn e ty) ~>p e'
    
  -- structural

  par-Var : {i : Fin n}
    -> (pVar i) ~>p pVar i
    
  par-TyU : pTyU ~>p pTyU
    
  par-Pi : {aTy aTy' : _} -> {bodTy bodTy' : _}
    -> aTy ~>p aTy' 
    -> bodTy ~>p bodTy'
    -> (pPi aTy bodTy) ~>p pPi aTy' bodTy'
    
  par-Fun :
    {bod bod' : _}
    -> bod ~>p bod'
    -> (pFun bod) ~>p pFun bod'
    
  par-App : {f f' a a' : _}
    -> f ~>p f'
    -> a ~>p a'
    -> (pApp f a) ~>p (pApp f' a')

  par-cast : {e e' : PreSyntax} -> {ty ty' : PreSyntax}
    ->  e ~>p e' 
    ->  ty ~>p ty' 
    -> (pAnn e ty) ~>p (pAnn e' ty')

par-refll : {n : ℕ}  (a : PreSyntax {n}) -> a ~>p a
par-refll (pVar i) = par-Var
par-refll pTyU = par-TyU
par-refll (pPi x x₁) = par-Pi (par-refll x) (par-refll x₁)
par-refll (pFun x) = par-Fun (par-refll x)
par-refll (pApp x x₁) = par-App (par-refll x) (par-refll x₁)
par-refll (pAnn x x₁) = par-cast (par-refll x) (par-refll x₁)

-- very influenced by https://plfa.github.io/Confluence/#parallel-reduction-satisfies-the-diamond-property
-- misleading name
-- the way this is presented, par-max may not be par, but instead withinexactly 2 par reductions away
par-max : {n : ℕ} -> PreSyntax {n} -> PreSyntax {n} 
par-max (pApp f@(pFun bod) a) = (par-max bod) [ o (par-max f) ] [ par-max a ]
par-max (pApp f a) = pApp (par-max f) (par-max a)
par-max (pVar i) = pVar i
par-max pTyU = pTyU
par-max (pPi aTy bodTy) = pPi (par-max aTy) (par-max bodTy)
par-max (pFun bod) = pFun (par-max bod)
par-max (pAnn e ty) = par-max e
    
postulate
  sub-par : {n : ℕ} {a a' : PreSyntax {suc n}} {b b' : PreSyntax {n}}
    -> a ~>p  a'
    -> b ~>p b'
    -> (a [ b ] ) ~>p  (a' [ b' ])

  o-par : {n : ℕ} {a a' : PreSyntax { n}} 
      -> a ~>p  a'
      -> o a ~>p  o a'

-- annoying name
par-triangle :  {n : ℕ} {a b : PreSyntax {n}}
   -> a ~>p b
   -> b ~>p (par-max a)
par-triangle (par-red par-arg par-bod)
  = sub-par (sub-par (par-triangle par-bod) (o-par (par-triangle (par-Fun par-bod)))) (par-triangle par-arg)
par-triangle (par-App  (par-Fun par-f) par-a)
  = par-red (par-triangle par-a) (par-triangle par-f)
par-triangle (par-cast-red par-e) = par-triangle par-e
par-triangle par-Var = par-Var
par-triangle par-TyU = par-TyU
par-triangle (par-Pi par-aTy par-bodTy) = par-Pi (par-triangle par-aTy) (par-triangle par-bodTy)
par-triangle (par-Fun par-bod) = par-Fun (par-triangle par-bod)
par-triangle (par-cast par-e _) = par-cast-red (par-triangle par-e)

-- applications spelled out, someday replace with 
-- par-triangle (par-App par-f par-a) = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-red x x₁) par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-cast-red x) par-a)
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-Var par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@par-TyU par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-Pi x x₁) par-a) 
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-App x x₁) par-a)
  = par-App (par-triangle par-f) (par-triangle par-a)
par-triangle (par-App par-f@(par-cast x x₁) par-a)
  = par-App (par-triangle par-f) (par-triangle par-a)

confulent-~> : {n : ℕ} {a b b' : PreSyntax {n}}
   -> a ~>p b
   -> a ~>p b'
   -> Σ _ \ v  -> b ~>p v  × b' ~>p v
confulent-~>  {_} {a} ab ab' = par-max a , par-triangle ab , par-triangle ab'




-- typed transitive reflective closuer
data _~>p*_ {n : ℕ}  : PreSyntax {n}  -> PreSyntax {n} -> Set  where
  par-refl : {m : _} -> m ~>p* m      -- TODO this could be admissable
    
  par-step : {a b c : _}
    -> a ~>p* b
    -> b ~>p c
    -> a ~>p* c

-- TODO is the strip lemma acuatlly needed or is it just an artifact of the encoding? not exactly
-- implicit is that the recursive result will preserve the dimension of tiles,  a single confluent step will wland within 1 step ot the corner
-- alternatively build up the tiling fronteer explicitly,
-- m : PreSyntax {n} -> ls : [a,m ~>p* a] -> exists v forall a <- fst ls, a ~>p* v
confulent-~>p* : {n : ℕ}  {m a a' : PreSyntax {n}}
   -> m ~>p* a
   -> m ~>p* a'
   -> Σ _ \ v  -> a ~>p* v × a' ~>p* v
confulent-~>p* {_} {m} {.m} {a'} par-refl ma' = a' , ma' , par-refl
confulent-~>p* {_} {m} {a} {.m}  ma par-refl = a , par-refl , ma
confulent-~>p* {_} {m} {a} {a'} (par-step m*b ba) (par-step m*b' b'a') = {!!}

data _|-_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n}  -> PreSyntax {n} -> Set


-- definitional eq
data  _|-_==_::_ {n : ℕ} (Γ : Ctx n) : PreSyntax {n} -> PreSyntax {n} -> PreSyntax {n} -> Set  where
  joinV : {n m m' ty : _}
    -> Γ |- m :: ty
    -> Γ |- m' :: ty
    -> m ~>p* n
    -> m' ~>p* n
    -> Γ |- m == m' :: ty

{-
stable-tyu :  {n : ℕ} {Γ : Ctx n}  {a  ty : _}
   -> Γ |- pTyU ~>*p a :: ty
   -> a ≡ pTyU
stable-tyu (par-refl x) = refl
stable-tyu (par-step rest step) with stable-tyu rest
stable-tyu (par-step rest par-TyU) | refl = refl


stable-pi :  {n : ℕ} {Γ : Ctx n}  {a aTy ty : _} {bodTy : _}
   -> Γ |- pPi aTy bodTy ~>*p a :: ty
   ->  Σ _ \ aTy'  -> Σ _ \ bodTy'  -> a ≡ pPi aTy' bodTy' 
stable-pi {n} {Γ}  {a} {aTy} {ty} {bodTy} (par-refl x) = aTy , bodTy , refl
stable-pi (par-step front step) with stable-pi front
stable-pi (par-step front (par-Pi step step₁)) | fst , xx = _ , _ , refl
-}


data _|-_::_ {n} Γ  where
  Var :  (v : Fin n) -> Γ |- pVar v :: lookup Γ v
  TyU : Γ |- pTyU :: pTyU
  Pi : { aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |- aTy :: pTyU ->  extCtx Γ aTy  |- bodTy :: pTyU
    -> Γ |-  pPi aTy bodTy :: pTyU
  Fun : { aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> {bod : PreSyntax }
    ->  Γ  |- aTy :: pTyU
    -> extCtx Γ  aTy |- bodTy :: pTyU
    -> extCtx (extCtx Γ aTy)  (o (pPi aTy bodTy)) |-  bod  :: o bodTy
     -> Γ |-  pFun bod  :: pPi aTy bodTy
  App : {f a aTy : PreSyntax } -> {bodTy : PreSyntax }
    -> Γ |-  f  :: pPi aTy bodTy -> Γ  |- a :: aTy 
    -> Γ |-  pApp f a  :: (bodTy [ a ])
  Cast : {e : PreSyntax } -> {ty : PreSyntax }
    -> Γ |-  e :: ty
    -> Γ |-  ty :: pTyU
    -> Γ |-  pAnn e ty  :: ty
    
  Conv : {a m m' : PreSyntax }
    -> Γ |-  a  :: m
    -> Γ |- m == m' :: pTyU
    -> Γ |-  a  :: m'


postulate
  ctx-wf :{n : ℕ} {Γ : Ctx n} {v : _} -> Γ |- lookup Γ v :: pTyU
  lookUp : {n : ℕ} (Γ : Ctx n) -> (i : Fin n)  ->  Σ _ \ a -> Γ |- a :: pTyU
-- preservation


postulate
  Tel : ℕ -> ℕ -> Set
  +++ : {n m : ℕ} (Γ : Ctx n) -> Tel n m -> Ctx (n + m)
--  _[_]tel : Tel n m
  
subst-ty : {!!} 
subst-ty = {!!}

-- needed to work around conv
--pi-ty-inv :{n : ℕ} {Γ : Ctx n} {b ATy : _} {BTy : _}
--  -> Γ |- pFun b :: e -> e === pPi ATy BTy
--  -> Γ ,, a ,, f |- b :: o BTy

_~>pctx_ : {n : ℕ} -> (Γ : Ctx n) -> (Γ' : Ctx n) -> Set -- TODO should be over prectx
Γ ~>pctx Γ' = (v : Fin _) -> lookup Γ v  ~>p  lookup Γ' v



preservation~>p :  {n : ℕ} {Γ : Ctx n} {a a' aTy : _}
  -> Γ |- a :: aTy -> a ~>p a'
  -> Γ |- a' :: aTy

-- TODO could rap this up in single recursion?
ctxstep-== : {n : ℕ} {Γ Γ' : Ctx n} {a a' aTy : _}
  -> Γ ~>pctx Γ' -> Γ |- a == a' :: aTy
  -> Γ' |- a == a' :: aTy
  
ctxstep-ty : {n : ℕ} {Γ Γ' : Ctx n} {a aTy : _}
  -> Γ ~>pctx Γ' -> Γ |- a :: aTy ->  Γ' |- a :: aTy
ctxstep-ty {_} {Γ} {Γ'} Γ-Γ' (Var v) = Conv (Var v) (joinV {!!} ? par-refl (par-step par-refl (Γ-Γ' v))) -- TODO need the ctx ok, so needs to be mutial with SR
  where
    lk : lookup Γ v ~>p lookup Γ' v
    lk = Γ-Γ' v
ctxstep-ty Γ-Γ' (Pi ty ty₁) = {!!}
ctxstep-ty Γ-Γ' (Fun ty ty₁ ty₂) = {!!}
ctxstep-ty Γ-Γ' (Conv ty eq) = Conv (ctxstep-ty  Γ-Γ' ty) (ctxstep-== Γ-Γ' eq)
ctxstep-ty Γ-Γ' (App ty ty₁) = App (ctxstep-ty Γ-Γ' ty) (ctxstep-ty Γ-Γ' ty₁)
ctxstep-ty Γ-Γ' (Cast ty ty₁) = Cast (ctxstep-ty Γ-Γ' ty) (ctxstep-ty Γ-Γ' ty₁)
ctxstep-ty Γ-Γ' TyU = TyU

ctxstep-== Γ-Γ' (joinV aTy a'Ty a-b a'-b) = joinV (ctxstep-ty Γ-Γ' aTy) (ctxstep-ty Γ-Γ' a'Ty) a-b a'-b


preservation~>p (Var v) par-Var = Var v
preservation~>p TyU par-TyU = TyU
preservation~>p  {_} {Γ} {pPi a b} {pPi a' b'} (Pi aty bty) (par-Pi a-a' b-b') = {!!}
  where
    a'ty : Γ |- a' :: pTyU
    a'ty = preservation~>p aty a-a'

    b'ty : extCtx Γ a |- b' :: pTyU
    b'ty = preservation~>p bty b-b'
    
    -- pPi a b' :: pTyU   which isn't particularly helpful
    -- need to allow typed step in ctx


preservation~>p (Fun Aty Bty bty) (par-Fun red) = Fun Aty Bty (preservation~>p bty red)
preservation~>p {_} {Γ} {pApp (pFun b) a}
  (App {_} {_} {ATy} {BTy} fty aty) (par-red {_} {a'} {_} {b'} a-a' b-b') = {!!}
  where
    a'ty : Γ |- a' :: ATy
    a'ty = preservation~>p aty a-a'
    
    b'ty :  {! Γ ,, f ,, ATy!} |- b' :: o BTy 
    b'ty = preservation~>p {!!} b-b' -- from inversion
    
    fun'ty : Γ |- pFun b' :: pPi ATy BTy 
    fun'ty = preservation~>p fty (par-Fun b-b')
  -- Γ |- (b' [ o (pFun b') ]) [ a' ] :: (BTy [ a ])
  --                                              by subst step-ty (or conversion), suffices to show
  -- Γ |- (b' [ o (pFun b') ]) [ a' ] :: (BTy [ a' ])
  -- Γ |- (b' [ o (pFun b') ]) [ a' ] :: (BTy [ a' ]) which follows by typed subst
  
preservation~>p {_} {Γ} {pApp f a} {pApp f' a'}
  (App {_} {_} {aTy} {bodTy} fty aty) (par-App f-f' a-a') = {!!}
  where
    a'ty : Γ |- a' :: aTy
    a'ty = preservation~>p aty a-a'
    f'ty : Γ |- f' :: pPi aTy bodTy
    f'ty = preservation~>p fty f-f'
  -- Γ |- f' a' :: (bodTy [ a  ])
  --                                              by subst step-ty (or conversion), suffices to show
  -- Γ |- f' a' :: (bodTy [ a' ]) by ty
preservation~>p {_} {Γ} {pAnn a A} (Cast aty Aty) (par-cast-red red) = preservation~>p aty red
preservation~>p {_} {Γ} {pAnn a A} (Cast aty Aty) (par-cast {_} {a'} {_} {A'} a-a' A-A') = final
  where
    a'ty : Γ |- a' :: A
    a'ty = preservation~>p aty a-a'
    a'ty' : Γ |- a' :: A'
    A'ty : Γ |- A' :: pTyU
    A'ty = preservation~>p Aty A-A'
    a'ty' = Conv a'ty (joinV Aty A'ty (par-step par-refl A-A') par-refl) -- (joinV (par-step (par-refl Aty) A-A') (par-refl A'ty))
    almost : Γ |- pAnn a' A' :: A'
    almost = Cast a'ty' A'ty
    final : Γ |- pAnn a' A' :: A
    final = Conv almost (joinV A'ty Aty par-refl (par-step par-refl A-A')) -- (joinV (par-refl A'ty) (par-step (par-refl Aty) A-A'))
preservation~>p (Conv ty x) red = Conv (preservation~>p ty red) x



{-

-- progress

data _val {n : ℕ} : PreSyntax {n} -> Set where
  vTyU : pTyU val
  vPi : { aTy : PreSyntax } -> {bodTy : PreSyntax }
     -> (pPi aTy bodTy) val
  vFun : {bod : PreSyntax {suc (suc n)} }
    -> (pFun bod) val
  -- TODO should casts be values?

data  _~>_ {n : ℕ} : PreSyntax {n} ->  PreSyntax {n} -> Set where
  app-red : {a  : PreSyntax} ->  {bod : PreSyntax {suc (suc n)} }
    ->  a val
    -> (pApp (pFun bod)  a) ~> ( bod [ o (pFun  bod) ] [ a ]  )
    
  cast-red : {e : PreSyntax} -> {ty : PreSyntax}
    ->  e val
    -> (pAnn e ty) ~> e
    
  -- structural
  appf-struc : {f f' a : PreSyntax } -> f ~> f' -> pApp f a ~> pApp f' a
  appa-struc : {f a a' : PreSyntax } -> f val -> a ~> a' -> pApp f a ~> pApp f a'
  
  cast-struc : {e e' : PreSyntax} -> {ty : PreSyntax}
    ->  e ~> e' 
    -> (pAnn e ty) ~> (pAnn e' ty) 
-}
