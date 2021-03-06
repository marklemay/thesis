module cast where

open import precast as p

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec   hiding (lookup ; [_])
open import Data.Sum  hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary -- using (¬_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])

{-
how do functions work? hard to substitute them!!!!!!!!!!!

specifically
\ x. 0 ~ \x. x in y => Vec (y 1)

-}

postulate
  --TODO bump up to presyntax
  _~~_ : {n : D} -> PreSyntax {n} -> PreSyntax {n} -> Set
  _~_spine_ : {d : D} -> PreSyntax {d} -> (v : Fin (D.tCon d)) -> {numArg : _} -> Vec (PreSyntax {d}) numArg -> Set


  Ctx : {D} -> Set
  InV : {d : D} -> (Γ : Ctx {d}) -> (v : Fin (D.var d))
    -> (ty : PreSyntax {d})
    -> Set
  InP : {d : D} -> (Γ : Ctx {d}) -> (v : Fin (D.pathV d))
    -> (l : PreSyntax {d})
    -> (r : PreSyntax {d})
    -> Set
  
  InTCon : {d : D} -> (Γ : Ctx {d}) -> (v : Fin (D.tCon d))
    ->  {n : _}
    -> (tel : p.PreTelUnit {d} {n})
    -> Set

data _|-_::_ {n : D} (Γ : Ctx {n}) : PreSyntax {n} -> PreSyntax {n} -> Set

--data _|-_:DC:_spine_ {d : D} (Γ : Ctx {d}) : PreSyntax {d} -> Fin (D.tCon d) -> {numArg : _} -> Vec ((PreSyntax {d})) numArg -> Set where

--data _|-_::_ {n : D} (Γ : Ctx {n}) : PreSyntax {n}  -> PreSyntax {n} -> Set


data _|-_::_~_ {n : D} (Γ : Ctx {n}) : PrePath {n} -> PreSyntax {n} -> PreSyntax {n} -> Set


data _|-_::_~_ {d} Γ where
  PVar :  (v : Fin (D.pathV d)) -> {l r : _} -> InP Γ v l r ->  Γ |- p.PVar v :: l ~ r
  Assert : {a a' : PreSyntax {d}} {l : Loc} {o :  p.Obs}
    -> {bod : PreSyntax {bind 1 d}}
  --  under specifically what conditions? 
    -> Γ |- Assert a a' l o bod :: (bod p.[ a ]) ~ ( bod p.[ a' ])
    -- TODO may need to split this up latterally so a/ a' can commute inside a constructor
    -- ...
  InTC : {tC : Fin (D.tCon d)} -> {numArgs : _ }
    -> (i : Fin numArgs) -> {tel : _} -> { InTCon Γ tC {numArgs} tel }
    -> {p : PrePath}
    -> {l r : PreSyntax}
    -> Γ |- p :: l ~ r
    
    -> {lArgs : _}
    -> {l ~ tC spine lArgs}
    -> {lArg : _}
    -> {lArgs [ i ]= lArg}
    
    -> {rArgs : _}
    -> {r ~ tC spine rArgs}
    -> {rArg : _}
    -> {rArgs [ i ]= rArg}

    -> Γ |- (p.InTC (toℕ i) p) :: lArg ~ rArg


    -- ...


  -- do paths support endpoint conversion?



data _|-_::_ {d} Γ where
  Var : (v : Fin (D.var d)) -> {ty : _} -> InV Γ v ty -> Γ |- p.Var v :: ty

  -- ...
  
  TyU : Γ |- pTyU :: pTyU
    

  Blame : {l r ty : PreSyntax } {p : _}
    -> Γ |- p :: l ~ r
    -- l =/= r
    -> Γ |- ty :: pTyU
    -> Γ |- Blame p :: ty
  

  Cast : {b uty ty : PreSyntax } 
    -> Γ |- b :: uty
    -> Γ |- uty :: pTyU
    -> {p : _}
    -> Γ |- p :: uty ~ ty
    -> Γ |- ty :: pTyU
    -> Γ |- Cast b uty p ty :: ty

  -- ...
  Conv : {a m m' : PreSyntax}
    -> Γ |-  a  :: m
    -> m ~~ m'
    -> Γ |-  a  :: m'


{-
data PrePath {d : D} : Set where
  Refl : PrePath
  Trans : PrePath {d} -> PrePath {d} -> PrePath {d}
  Rev : PrePath {d} -> PrePath {d}
  InTC : ℕ -> PrePath {d} -> PrePath {d}
  InC : ℕ -> PrePath {d} -> PrePath {d}
  UncastL : PrePath {d} -> PrePath {d}
  UncastR : PrePath {d} -> PrePath {d}

  Pi : {aty : PreSyntax } -> {bodty : PreSyntax }
    -> (aTy : Γ |- aty :: pTyU)
    -> (bodTy : Ext Γ aty |- bodty :: pTyU)
    -> Γ |-  pPi aty bodty :: pTyU

  Fun : { aty : PreSyntax } -> {bodty : PreSyntax }
    -> {bod : PreSyntax }
    -- -> (aTy : Γ  |- aty :: pTyU)
    -- -> (bodTy : Ext Γ aty |- bodty :: pTyU)
    -> Ext (Ext Γ aty) (o (pPi aty bodty)) |- bod :: o bodty
    -> Γ |- pFun bod :: pPi aty bodty
    
  App : {f a aty : PreSyntax } -> {bodty : PreSyntax }
    -> Γ |-  f  :: pPi aty bodty -> Γ |- a :: aty 
    -> Γ |-  pApp f a  :: (bodty [ a ])



data PrePat {d} : Set where
  patVar : PrePat
  patCon : (i : Fin (D.var d))
    -> Data.List.List (PrePat {d})
    -- and a pathVar!
    -> PrePat

bindPats :  (d : D) -> {i :  _} -> (Vec (PreSyntax {d}) i) -> D
bindPats = {!!}

data PreSyntax {d} where
  Var : (i : Fin (D.var d)) -> PreSyntax
  TCon : (i : Fin (D.tCon d)) -> PreSyntax
  Con : (i : Fin (D.con d)) -> PreSyntax

  Case : {i :  _}
    -> (scruts : Vec (PreSyntax {d}) i)
    -- TAS motive?
    -> Data.List.List ( Σ (Vec (PreSyntax {d}) i) λ p → PreSyntax {bindPats d p} )
    -> Data.List.List (Vec (PreSyntax {d}) i)
    -> PreSyntax
  Cast :(bod : PreSyntax {d}) -> PrePath {d} -> PreSyntax
  
  pTyU : PreSyntax
  
  pPi : PreSyntax {d} -> PreSyntax {bind 1 d} -> PreSyntax
  pFun : (bod : PreSyntax {bind 2 d}) -> PreSyntax
  
  pApp :  PreSyntax {d} -> PreSyntax {d} -> PreSyntax
-}




{-

--  Ctx  : ℕ -> Set -- assume ctxs were well formed by consnstruction
--  Emp : Ctx 0

data Ctx : {n : ℕ} -> Set


postulate
  reg :  {n : ℕ} -> {Γ : Ctx {n}} -> CtxOK Γ -> {a aty : PreSyntax } -> Γ |- a :: aty -> Γ |- aty :: pTyU
-}
