module SolverFrontend where

-- usual modules

open import Data.Bool
open import Data.Empty
open import Data.Fin using (Fin;zero;suc;#_;fromℕ≤)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤;tt)
open import Data.Vec renaming (reverse to vreverse)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- semiring solver and reflection

-- open SemiringSolver
open import Data.Bool.Properties

import Data.Bool.NP

open import Data.Vec.N-ary
open import Reflection

--------------------------------------------
--  Extracting two sides of the equation  --
--------------------------------------------

≡' : Name
≡' = quote _≡_

zero' : Name
zero' = quote Data.Nat.zero

suc' : Name
suc' = quote Data.Nat.suc

plus' : Name
plus' = quote Data.Nat._+_

mult' : Name
mult' = quote Data.Nat._*_

--------------------------------------------------
--  Extracting the universally quantified nats  --
--------------------------------------------------
-- returns the number of the outermost pi quantified variables.

argsNo : Term → ℕ
argsNo (pi t₁ (el s t)) = suc (argsNo t)
argsNo (var x args) = 0
argsNo (con c args) = 0
argsNo (def f args) = 0
argsNo (lam v t) = 0
argsNo (sort x) = 0
argsNo unknown = 0

quote-ℕ : ℕ -> Term
quote-ℕ zero = con (quote Data.Nat.zero) []
quote-ℕ (suc n) = con (quote Data.Nat.suc) ((arg visible relevant (quote-ℕ n)) ∷ [])

unsafe-quote-Fin : ℕ → Term
unsafe-quote-Fin zero = con (quote Fin.zero) []
unsafe-quote-Fin (suc n) = con (quote Fin.suc) ((arg visible relevant (unsafe-quote-Fin n)) ∷ [])

{-
All : (P : Term -> Set) → List (Arg Term) → Set
All P xs = {!!}

isOkP : Term -> Set
isOkP (var x args) = ⊤
isOkP (con c args) = ⊥
isOkP (def f []) = ⊥
isOkP (def f (x ∷ [])) = ⊥
isOkP (def f (x ∷ x₁ ∷ [])) = check f x x₁ where
  check : Name -> Arg Term -> Arg Term -> Set
  check f (arg _ _ x) (arg _ _ y) with f ≟-Name plus'
  ... | yes _ = isOkP x × isOkP y
  ... | no _  = ⊥
isOkP (def f (x ∷ x₁ ∷ x₂ ∷ args)) = ⊥
isOkP (lam v t) = ⊥
isOkP (pi t₁ t₂) = ⊥
isOkP (sort x) = ⊥
isOkP unknown = ⊥
-}

isOk : Term -> Set
isOk (var x args) = ⊥
isOk (con c args) = ⊥
isOk (def f []) = ⊥
isOk (def f (x ∷ [])) = ⊥
isOk (def f (x ∷ x₁ ∷ [])) = ⊥
isOk (def f (x ∷ x₁ ∷ x₂ ∷ [])) = ⊥
isOk (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])) = checkIt f x₂ x₃ where
  checkIt : Name -> Arg Term -> Arg Term -> Set
  checkIt f (arg _ _ x) (arg _ _ y) with f ≟-Name ≡'
  ... | yes _ = ⊤
  ... | no _ = ⊥
isOk (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args)) = ⊥
isOk (lam v t) = ⊥
isOk (pi t₁ (el s t)) = isOk t
isOk (sort x) = ⊥
isOk unknown = ⊥

module Dummy (plus' : Name)(nrArgs : ℕ) where
  open import Experiment
  module M = Syntax nrArgs

  translateP : (t : Term) -> Term
  translateM : List (Arg Term) -> List (Arg Term)

  translateP (var x args) = con (quote Syntax.var) (arg visible relevant (unsafe-quote-Fin x) ∷ [])
  translateP (con c args) {- with c ≟-Name suc'
  ... | yes _ = def (quote _:+_) ( arg visible relevant (quoteTerm (Polynomial.con {nrArgs} 1) ) -- con (quote Polynomial.con) (arg visible relevant (quoteTerm 1) ∷ []))
                                 ∷ translateM args)
  ... | no  _ -} = def (quote Syntax.con) (arg visible relevant (quote-ℕ nrArgs) ∷ (arg visible relevant (con c args)) ∷ [])
  translateP (def f args) with f ≟-Name plus' 
  ... | yes _ = con (quote Syntax._+_) (translateM args)
  ... | no _  = con (quote Syntax.con) (arg visible relevant (def f args) ∷ [])
  translateP (lam v t)  = unknown
  translateP (pi t₁ t₂) = unknown
  translateP (sort x)   = unknown
  translateP unknown    = unknown

  translateM [] = []
  translateM (arg v r x ∷ xs) = (arg v r (translateP x)) ∷ (translateM xs)

  translate : (t : Term) -> isOk t -> Term × Term
  translate (var x args) ()
  translate (con c args) ()
  translate (def f []) ()
  translate (def f (x ∷ [])) ()
  translate (def f (x ∷ x₁ ∷ [])) ()
  translate (def f (x ∷ x₁ ∷ x₂ ∷ [])) ()
  translate (def f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ x₃ ∷ [])) isOk with f ≟-Name ≡' 
  ... | yes _ = (translateP x₂) , translateP x₃
  translate (def f (x ∷ x₁ ∷ arg v r x₂ ∷ arg v₁ r₁ x₃ ∷ [])) () | no ¬p
  translate (def f (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ args)) ()
  translate (lam v t) ()
  translate (pi t₁ (el s t)) isOk = translate t isOk
  translate (sort x) ()
  translate unknown ()

open import Experiment

mkLam : (n : ℕ) → Term → Term
mkLam zero tm = tm
mkLam (suc n) tm = lam visible (mkLam n tm)

mkArgs : ℕ → Term
mkArgs = go 0 where
  go : ℕ → ℕ → Term                
  go a zero    = con (quote Vec.[]) []
  go a (suc n) = con (quote Vec._∷_) ((arg visible relevant (var a [])) ∷ ((arg visible relevant (go (suc a) n)) ∷ []))

ringu : (t : Term) -> isOk t -> Term
ringu t isOk = mkLam (argsNo t) (
              def (quote Syntax.solve) ((arg visible relevant (quote-ℕ (argsNo t)))
            ∷ arg visible relevant (mkArgs (argsNo t))  
            ∷ arg visible relevant (proj₁ tms)
            ∷ arg visible relevant (proj₂ tms)
            ∷ arg visible relevant (con (quote tt) [])
            ∷ [])) where
  tms = (Dummy.translate (quote _xor_) (argsNo t) t isOk)
 
postulate 
  f : ℕ -> ℕ
-- {-
lemma3 : ∀ m n → m xor n ≡ n xor m
lemma3 = quoteGoal e in unquote (ringu e _)
  
-- -}
import Level

{- BUG
lemma5 : ∀ m n x y → m xor true xor y xor (n xor true) ≡ y xor x xor x xor n xor m
lemma5 = quoteGoal e in unquote (ringu e _)
-- -}

lemma4 : ∀ m n → false xor m xor n ≡ n xor m
lemma4 m n = solve (n ∷ m ∷ []) (var (suc zero) Tm.+ var zero) (var zero Tm.+ var (suc zero)) _ where
  open Syntax 2

test : 5 ≡ 5
test = unquote (con (quote refl) []) 

{-
lemma3 : ∀ m n → suc (m + n + (m + n)) ≡ m + m + suc (n + n)
lemma3 = quoteGoal e in unquote (ringu e)
-}