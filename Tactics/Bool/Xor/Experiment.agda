module Experiment where

open import Data.Nat using (ℕ ; zero ; suc) 
open import Data.Vec hiding (_∈_)
open import Data.Bool.NP renaming (_==_ to _=='_)
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Nullary

open import Data.Product using (Σ ; proj₁ ; proj₂)

module MOVE'EM where
  open import Data.Fin using (Fin ; suc ; zero)

  dXor : (x : Bool) → x xor x ≡ false
  dXor true = refl
  dXor false = refl

  dNot : (x : Bool) → x ≡ not (not x)
  dNot true = refl
  dNot false = refl

  sNot : (x y : Bool) → not x xor y ≡ not (x xor y)
  sNot true y = dNot y
  sNot false y = refl

  sNot' : (x y : Bool) → x xor not y ≡ not (x xor y)
  sNot' true y = refl
  sNot' false y = refl
  
  rmSuc≡ : {n : ℕ}{i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
  rmSuc≡ refl = refl

  rmSuc : {n : ℕ} → (x y : Fin n) → Fin.suc x ≢ suc y → x ≢ y
  rmSuc x .x neq refl = neq refl 

  sym≢ : {A : Set}{x y : A} → x ≢ y → y ≢ x
  sym≢ p = λ x → p (sym x)

  cong≢ : {A B : Set}(f : A → B)(inj : {x y : A} → f x ≡ f y → x ≡ y){x y : A} → x ≢ y → f x ≢ f y
  cong≢ f inj x≢y fx≡fy = x≢y (inj fx≡fy)

  dXor3 : ∀ x {y z} → y ≡ z → x xor x xor y ≡ z
  dXor3 true refl = sym (dNot _)
  dXor3 false refl = refl
 
  =='toxor : ∀ x y → x ==' y ≡ not (x xor y)
  =='toxor true true = refl
  =='toxor true false = refl
  =='toxor false true = refl
  =='toxor false false = refl

  _[_:=_] : {A : Set}{n : ℕ} → Vec A n → Fin n → (A → A) → Vec A n
  []       [ ()    := f ]
  (x ∷ xs) [ zero  := f ] = f x ∷ xs
  (x ∷ xs) [ suc i := f ] = x ∷ xs [ i := f ]

  flip : {n : ℕ} → Fin n → Vec Bool n → Vec Bool n
  flip i xs = xs [ i := not ]

  data _·_∈_ {A : Set}(x : A) : {n : ℕ} → ℕ → Vec A n → Set where
    []  : x · 0 ∈ []
    x∷_ : {n : ℕ}{occ : ℕ}{xs : Vec A n} → x · occ ∈ xs → x · (suc occ) ∈ (x ∷ xs)
    _∷_ : {n : ℕ}{occ : ℕ}{y : A}{xs : Vec A n} → x ≢ y → x · occ ∈ xs → x · occ ∈ (y ∷ xs)
  
  _∉_ : {A : Set}{n : ℕ} → A → Vec A n → Set
  x ∉ xs = x · 0 ∈ xs

  _U∈_ : {A : Set}{n : ℕ} → A → Vec A n → Set
  x U∈ xs = x · 1 ∈ xs


  lookupFalse : {A : Set}(x : A){n : ℕ} → (i : Fin n) → lookup i (replicate x) ≡ x 
  lookupFalse x zero = refl
  lookupFalse x (suc i) = lookupFalse x i

  lookup[:=] : {A : Set}{n : ℕ}(f : A → A)(i : Fin n)(xs : Vec A n) → lookup i (xs [ i := f ]) ≡ f (lookup i xs)
  lookup[:=] f zero    (x ∷ xs) = refl
  lookup[:=] f (suc i) (x ∷ xs) = lookup[:=] f i xs

  lookupFlip : {n : ℕ}(x : Fin n)(xs : Vec Bool n) → lookup x (flip x xs) ≡ not (lookup x xs)
  lookupFlip = lookup[:=] not

  open import Data.Empty

  lookup≢[:=] : {A : Set}{n : ℕ}(f : A → A)(x y : Fin n)(xs : Vec A n) → x ≢ y → lookup x (xs [ y := f ]) ≡ lookup x xs
  lookup≢[:=] _ zero zero (x ∷ xs) x≢y = ⊥-elim (x≢y refl)
  lookup≢[:=] _ zero (suc y) (x ∷ xs) x≢y = refl
  lookup≢[:=] _ (suc x) zero (x₁ ∷ xs) x≢y = refl
  lookup≢[:=] f (suc x) (suc y) (x₁ ∷ xs) x≢y = lookup≢[:=] f x y xs (rmSuc x y x≢y)

  lookupDis : {n : ℕ}(x y : Fin n)(xs : Vec Bool n) → x ≢ y → lookup x (flip y xs) ≡ lookup x xs
  lookupDis = lookup≢[:=] not

  tabLem : {A : Set}{n : ℕ}(i : Fin n)(f : Fin n → A) → f i ≡ lookup i (tabulate f)
  tabLem zero f    = refl
  tabLem (suc i) f = tabLem i (λ x → f (suc x))

  inAll≡ : {n : ℕ}(i : Fin n) → i ≡ lookup i (allFin n)
  inAll≡ i = tabLem i (λ x → x)

  notIn : {A : Set}{n : ℕ}{x : A}(xs : Vec A n) → ((j : Fin n) → x ≢ lookup j xs) → x ∉ xs
  notIn [] fun = []
  notIn (x₁ ∷ xs) fun = (fun zero) ∷ (notIn xs (λ j → fun (suc j)))

  isIn : {A : Set}{n : ℕ}{x : A}(i : Fin n)(xs : Vec A n) → ((j : Fin n) → x ≡ lookup j xs → i ≡ j) → x ≡ lookup i xs → x U∈ xs
  isIn (zero {n}) (x₁ ∷ xs) neq refl = x∷ (notIn xs fun) where
    fun : (j : Fin n) → x₁ ≢ lookup j xs
    fun j eq with neq (suc j) eq
    ... | ()
  isIn {A} (suc {n} i) (x₁ ∷ xs) neq eq = _∷_ (x≢x₁ neq) (isIn i xs (λ j x → rmSuc≡ (neq (suc j) x)) eq) where
    x≢x₁ : ∀ {x x₁ : A} → ((j : Fin (suc n)) → x ≡ lookup j (x₁ ∷ xs) → suc i ≡ j) → x ≢ x₁
    x≢x₁ neq' refl with neq' zero refl
    x≢x₁ neq' refl | ()

  inAll : {n : ℕ}(i : Fin n) → i U∈ allFin n
  inAll i = isIn i (allFin _) (λ j x → trans x (sym (inAll≡ j))) (inAll≡ i)
 



module Reduction (Tm : Set)(Res : Set)(eval : Tm → Res) where
  _≈_ : Tm → Tm → Set
  tm ≈ tm' = eval tm ≡ eval tm'

  record NormBase (Norm : Tm → Set)(tm : Tm) : Set where
    constructor _⊢_
    field
      {wit} : Tm
      eq    : tm ≈ wit
      ntm   : Norm wit

  open NormBase public

  Reify : {Norm : Tm → Set} → ((tm : Tm) → NormBase Norm tm) → Set
  Reify normal = (tm tm' : Tm) →
                   NormBase.wit (normal tm) ≈ NormBase.wit (normal tm') → tm ≈ tm'

  Reify≡ : {Norm : Tm → Set} → ((tm : Tm) → NormBase Norm tm) → Set
  Reify≡ normal = (tm tm' : Tm) →
                   NormBase.wit (normal tm) ≡ NormBase.wit (normal tm') → tm ≈ tm'

  NormKit : (Norm : Tm → Set) → Set
  NormKit Norm = (tm : Tm) → NormBase Norm tm

  infixl 5 _⊢N_

  _→N_ : (_ _ : Tm → Set) → Set
  N₁ →N N₂ = {tm : Tm} → N₁ tm → NormBase N₂ tm

  _⊢N_ : {N₁ N₂ : Tm → Set} → NormKit N₁ → (N₁ →N N₂) → NormKit N₂
  _⊢N_ ⟦_⟧ tran tm with ⟦ tm ⟧
  ... | eq ⊢ ntm with tran ntm
  ... | eq' ⊢ ntm' = (trans eq eq') ⊢ ntm'

  idTran : {N₁ : Tm → Set} → N₁ →N N₁
  idTran red = refl ⊢ red

  idKit : NormKit (λ _ → Tm)
  idKit tm = record { wit = tm ; eq = refl ; ntm = tm }

  reify-normkit : ∀ {Norm} → (normal : NormKit Norm) → Reify normal
  reify-normkit ⟦_⟧ tm tm' ⟦tm⟧≈⟦tm'⟧ = trans (NormBase.eq ⟦ tm ⟧) (trans ⟦tm⟧≈⟦tm'⟧ (sym (NormBase.eq ⟦ tm' ⟧)))

  reify≡-normkit : ∀ {Norm} → (normal : NormKit Norm) → Reify≡ normal
  reify≡-normkit ⟦_⟧ tm tm' ⟦tm⟧≡⟦tm'⟧ = trans (eq ⟦ tm ⟧) (trans (cong eval ⟦tm⟧≡⟦tm'⟧) (sym (eq ⟦ tm' ⟧)))

module Reduction-NP (Tm : Set)(eval : Tm → Bool) where
  open Reduction Tm Bool eval public 

  spec-reify : ∀ {Norm} (normal : NormKit Norm) → (tm : Tm) → T (eval (NormBase.wit (normal tm))) → T (eval tm)
  spec-reify ⟦_⟧ tm T⟦tm⟧ = subst T (sym (eq ⟦ tm ⟧)) T⟦tm⟧

module Syntax (nrVars : ℕ) where

  open import Data.Fin public using (Fin ; zero ; suc)

  Var = Fin nrVars

  data Tm : Set where
    var   : Var → Tm
    _+_ _==_  : Tm → Tm → Tm
    -_    : Tm → Tm
    0# 1# : Tm

  con : Bool → Tm
  con true  = 1#
  con false = 0#

  module WithEnv (G : Vec Bool nrVars) where
    eval : Tm → Bool
    eval (var x)     = lookup x G
    eval (tm + tm₁)  = eval tm xor eval tm₁
    eval (tm == tm') = eval tm ==' eval tm'
    eval (- tm)      = not (eval tm)
    eval 0#          = false
    eval 1#          = true

    open Reduction-NP Tm eval
  
    open MOVE'EM

    data NormalTm : Tm → Set where
      0# : NormalTm 0#
      1#:+_ : {tm : Tm} → NormalTm tm → NormalTm (1# + tm)
      var_:+_ : {tm : Tm} → (v : Var) → NormalTm tm → NormalTm (var v + tm)
 
    _:++_ : {tm tm' : Tm} → NormalTm tm → NormalTm tm' → NormBase NormalTm (tm + tm')
    0#            :++ ys = refl ⊢ ys
    _:++_ {tm' = tm'} (1#:+_ {tm} xs) ys with xs :++ ys
    ... | p ⊢ n = trans (sNot (eval tm) (eval tm')) (cong not p) ⊢ (1#:+ n)
    (var v :+ xs) :++ ys with xs :++ ys
    ... | p ⊢ n = trans (Xor°.+-assoc (lookup v G) _ _) (cong (λ P → lookup v G xor P) p) ⊢ (var v :+ n)

    normal : NormKit NormalTm 
    normal (var x) = sym (proj₂ Xor°.+-identity _) ⊢ (var x :+ 0#)
    normal (tm + tm') with normal tm | normal tm'
    ... | p ⊢ n | p' ⊢ n' with n :++ n'
    ... | p'' ⊢ n'' = trans (cong₂ _xor_ p p') p'' ⊢ n''
    normal (tm == tm') with normal tm | normal tm'
    ... | p ⊢ n | p' ⊢ n' with n :++ n'
    ... | p'' ⊢ n'' = trans (=='toxor (eval tm) (eval tm')) (cong not (trans (cong₂ _xor_ p p') p'')) ⊢ (1#:+ n'')
      -- cong not (trans (trans {!!} (cong₂ _xor_ p p')) p'') ⊢ 1#:+ n''
    normal (- tm) with normal tm
    ... | p ⊢ n = cong not p ⊢ (1#:+ n)
    normal 0# = refl ⊢ 0#
    normal 1# = refl ⊢ (1#:+ 0#)

    open import Data.Product

    data Normal1Tm : Tm → Set where
      0# : Normal1Tm 0#
      var_:+_ : {tm : Tm} → (x : Var) → Normal1Tm tm → Normal1Tm (var x + tm)

    data Norm1Tm (Norm : Tm → Set) : Tm → Set where
      0#:+_ : {tm : Tm} → Norm tm → Norm1Tm Norm tm
      1#:+_ : {tm : Tm} → Norm tm → Norm1Tm Norm (1# + tm)

    tranNorm : {N₁ N₂ : Tm → Set} → N₁ →N N₂ → Norm1Tm N₁ →N Norm1Tm N₂
    tranNorm red (0#:+ x) with red x
    ... | eq ⊢ x' = eq ⊢ 0#:+ x'
    tranNorm red (1#:+ x) with red x
    ... | eq ⊢ x' = cong not eq ⊢ 1#:+ x'

    tran : NormalTm →N Norm1Tm Normal1Tm
    tran 0#                  = refl ⊢ (0#:+ 0#)
    tran (1#:+ norm)     with tran norm
    ... | eq ⊢ 0#:+ x        = cong not eq ⊢ 1#:+ x
    ... | eq ⊢ 1#:+_ {tm₁} x = trans (cong not eq) (sym (dNot (eval tm₁))) ⊢ (0#:+ x)
    tran (var v :+ norm) with tran norm
    ... | eq ⊢ 0#:+ x        = cong (λ x₁ → lookup v G xor x₁) eq ⊢ (0#:+ (var v :+ x))
    ... | eq ⊢ 1#:+ x        = trans (cong (λ x₁ → lookup v G xor x₁) eq) (sNot' (lookup v G) _) ⊢ (1#:+ (var v :+ x))

    sumP : {n : ℕ} → Vec (Fin nrVars) n → Vec Bool nrVars → Tm
    sumP [] xs = 0#
    sumP (x ∷ is) xs with lookup x xs
    ... | true  = var x + sumP is xs
    ... | false = sumP is xs

    data Normal2Tm : Tm → Set where
      N2  : (xs : Vec Bool nrVars) → Normal2Tm (sumP (allFin nrVars) xs)

    tran' : Normal1Tm →N Normal2Tm
    tran' 0#              = lem (allFin nrVars) ⊢ N2 (replicate false)
      where
        lem : {n : ℕ}(is : Vec (Fin nrVars) n) → false ≡ eval (sumP is (replicate false))
        lem []       = refl
        lem (x ∷ is) rewrite lookupFalse false x = lem is
    tran' (var x :+ norm) with tran' norm
    ... | eq ⊢ N2 xs = trans (cong (λ x₁ → lookup x G xor x₁) eq) (lem (inAll x)) ⊢ N2 (flip x xs)
      where
        not-in : {n : ℕ}(x : Fin nrVars)(is : Vec (Fin nrVars) n) → x ∉ is → eval (sumP is xs) ≡ eval (sumP is (flip x xs))
        not-in x₁ [] x∉xs        = refl
        not-in x₁ (x₂ ∷ is) (x₁≢x₂ ∷ x∉xs) rewrite lookupDis x₂ x₁ xs (sym≢ x₁≢x₂) with lookup x₂ xs
        ... | true  = cong (λ x₃ → lookup x₂ G xor x₃) (not-in x₁ is x∉xs)
        ... | false = not-in x₁ is x∉xs

        lem : {n : ℕ}{is : Vec (Fin nrVars) n} → x U∈ is
            → lookup x G xor eval (sumP is xs) ≡ eval (sumP is (flip x xs))
        lem (x∷_ {n} .{0} {xs₁} elem) rewrite lookupFlip x xs with lookup x xs 
        ... | true  = dXor3 (lookup x G) (not-in x xs₁ elem)
        ... | false = cong (λ x₁ → lookup x G xor x₁) (not-in x xs₁ elem)
        lem (_∷_ {n} {.1} {y} {xs₁} x≢y elem) rewrite lookupDis y x xs (sym≢ x≢y) with lookup y xs
        ... | true  = lookup x G xor (lookup y G xor eval (sumP xs₁ xs)) ≡⟨ sym (Xor°.+-assoc (lookup x G) (lookup y G) (eval (sumP xs₁ xs))) ⟩ 
                      (lookup x G xor lookup y G) xor eval (sumP xs₁ xs) ≡⟨ cong (λ x₁ → x₁ xor eval (sumP xs₁ xs)) (Xor°.+-comm (lookup x G) (lookup y G)) ⟩
                      (lookup y G xor lookup x G) xor eval (sumP xs₁ xs) ≡⟨ Xor°.+-assoc (lookup y G) (lookup x G) (eval (sumP xs₁ xs)) ⟩
                      lookup y G xor (lookup x G xor eval (sumP xs₁ xs)) ≡⟨ cong (λ P → lookup y G xor P) (lem elem) ⟩
                      lookup y G xor eval (sumP xs₁ (flip x xs)) ∎  where open ≡-Reasoning
        ... | false = lem elem

    nf = normal ⊢N tran ⊢N tranNorm tran'
  
    reify = reify-normkit nf
    reify≡ = reify≡-normkit nf

    cool : ∀ x y → T (x ==' y) → x ≡ y
    cool true true _ = refl
    cool true false ()
    cool false true ()
    cool false false _ = refl 

    solve : (tm tm' : Tm) → T (eval (NormBase.wit (nf (tm == tm')))) → eval tm ≡ eval tm'
    solve tm tm' pr = cool (eval tm) (eval tm') (spec-reify nf (tm == tm') pr)

  open WithEnv public

example :  ∀ x y → (x xor true) xor (x xor y) ≡ true xor (x xor (y xor x))
example x y = solve 2 (x ∷ y ∷ []) (((var zero) + 1#) + (var zero + (var (suc zero)))) (1# + ((var zero) + (var (suc zero) + var zero))) _
  where open Syntax