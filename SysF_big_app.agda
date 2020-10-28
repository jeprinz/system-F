open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit

------------ Step 1: define Δ and four type families Δ → Set, ITC, A, Γ, and Δpre

Δ = ℕ
-- same as Fin
data InTypeCtx : Δ → Set where
  same : ∀{Δ₁} → InTypeCtx (suc Δ₁)
  next : ∀{Δ₁} → InTypeCtx Δ₁ → InTypeCtx (suc Δ₁)

Δat : ∀{Δ₁} → (itc : InTypeCtx Δ₁) → Δ
Δat {suc Δ₁} same = Δ₁
Δat {suc Δ₁} (next itc) = Δat itc

data A : Δ → Set where
  var : ∀{Δ₁} → InTypeCtx Δ₁ → A Δ₁
  4all : ∀{Δ₁} → A (suc Δ₁) → A Δ₁
  _⇒_ : ∀{Δ₁} → A Δ₁ → A Δ₁ → A Δ₁
  𝟚 : ∀{Δ₁} → A Δ₁

data Γ : Δ → Set where
  ∅ : ∀ {Δ₁} → Γ Δ₁
  _,_ : ∀ {Δ₁} → (Γ₁ : Γ Δ₁) → A Δ₁ → Γ Δ₁

data Δpre : Δ → Set where -- represents a prefix Δ₁
  same : ∀{Δ₁} → Δpre Δ₁
  next : ∀{Δ₁} → Δpre Δ₁ → Δpre (suc Δ₁)

ΔpreAt : ∀{Δ₁} → Δpre Δ₁ → Δ
ΔpreAt {Δ₁} same = Δ₁
ΔpreAt (next pre) = ΔpreAt pre

------------------- Step 2: define weakening for each family
-- If P could be of Exp type, could define this and save a lot of work:
-- ΔweakenAnything : ∀{P : Δ → Set} → ∀{Δ₁} → (pre : Δpre Δ₁) → P Δ₁ → P (ΔweakenΔ pre)
-- ΔweakenAnything = {!   !}

-- This really just adds one, but in a sufficiently typed way to
-- make subsequent things easier
ΔweakenΔ : {Δ₁ : Δ} → Δpre Δ₁ → Δ
ΔweakenΔ {Δ₁} same = suc Δ₁
ΔweakenΔ (next pre) = suc (ΔweakenΔ pre)

ΔweakenITC : ∀{Δ₁} → (pre : Δpre Δ₁) → InTypeCtx Δ₁ → InTypeCtx (ΔweakenΔ pre)
ΔweakenITC same itc = next itc
ΔweakenITC (next pre) same = same
ΔweakenITC (next pre) (next itc) = next (ΔweakenITC pre itc)

ΔweakenA : ∀{Δ₁} → (pre : Δpre Δ₁) → A Δ₁ → A (ΔweakenΔ pre)
ΔweakenA pre (var x) = var (ΔweakenITC pre x)
ΔweakenA pre (4all A₁) = 4all (ΔweakenA (next pre) A₁)
ΔweakenA pre (A₁ ⇒ A₂) = (ΔweakenA pre A₁) ⇒ (ΔweakenA pre A₂)
ΔweakenA pre 𝟚 = 𝟚

ΔweakenΓ : ∀{Δ₁} → (pre : Δpre Δ₁) → Γ Δ₁ → Γ (ΔweakenΔ pre)
ΔweakenΓ pre ∅ = ∅
ΔweakenΓ pre (Γ₁ , A₁) = (ΔweakenΓ pre Γ₁) , (ΔweakenA pre A₁)

ΔweakenΔpre : ∀{Δ₁} → (pre toWeaken : Δpre Δ₁) → Δpre (ΔweakenΔ pre)
ΔweakenΔpre same toWeaken = next toWeaken
ΔweakenΔpre (next pre) same = same
ΔweakenΔpre (next pre) (next toWeaken) = next (ΔweakenΔpre pre toWeaken)

--------------- Step 3: define substitution for some types (do I need it for more?)

-- really just subtracts one
ΔsubΔ : ∀{Δ₁} → InTypeCtx Δ₁ → Δ
ΔsubΔ {suc Δ₁} same = Δ₁
ΔsubΔ {suc Δ₁} (next itc) = suc (ΔsubΔ itc)

-- data _prefixTC_ : Δ → Δ → Set where
--   same : ∀{Δ₁} → Δ₁ prefixTC Δ₁
--   next : ∀{Δ₁ Δ₁'} → Δ₁ prefixTC Δ₁' → Δ₁ prefixTC (suc Δ₁')

ΔsubA : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : A (Δat itc)) → A Δ₁ → A (ΔsubΔ itc)
ΔsubA same toSub (var same) = toSub
ΔsubA same toSub (var (next itc')) = var itc'
ΔsubA (next itc) toSub (var same) = var same
ΔsubA (next itc) toSub (var (next itc')) = ΔweakenA same (ΔsubA itc toSub (var itc'))
ΔsubA itc toSub (4all T) = 4all (ΔsubA (next itc) toSub T)
ΔsubA itc toSub (A ⇒ B)
  = (ΔsubA itc toSub A) ⇒ (ΔsubA itc toSub B)
ΔsubA itc toSub 𝟚 = 𝟚

ΔsubΓ : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : A (Δat itc)) → Γ Δ₁ → Γ (ΔsubΔ itc)
ΔsubΓ itc toSub ∅ = ∅
ΔsubΓ itc toSub (Γ₁ , T)
  = (ΔsubΓ itc toSub Γ₁) , (ΔsubA itc toSub T)

-- Above this line is stuff that depends on Δ
------------------------------------------------------------------------
-- Below this line is Δ and Γ

data InCtx : {Δ₁ : Δ} → Γ Δ₁ → Set where
  same : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {T : A Δ₁} → InCtx (Γ₁ , T)
  next : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {Next : A Δ₁} → InCtx {Δ₁} Γ₁ → InCtx (Γ₁ , Next)

Tat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → A Δ₁
Tat (same {_} {_} {T}) = T
Tat (next icx) = Tat icx


ΔweakenICX : ∀{Δ₁} → (pre : Δpre Δ₁) → {Γ₁ : Γ Δ₁}
  → InCtx Γ₁ → InCtx (ΔweakenΓ pre Γ₁)
ΔweakenICX pre same = same
ΔweakenICX pre (next icx) = next (ΔweakenICX pre icx)

ΓsubΓ : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → (icx : InCtx Γ₁) → Γ Δ₁
ΓsubΓ {_} {Γ₁ , T} same = Γ₁
ΓsubΓ {_} {Γ₁ , T} (next icx) = (ΓsubΓ icx) , T

data Exp : {Δ₁ : Δ} → Γ Δ₁ → A Δ₁ → Set where
  lambda : ∀{Δ₁ Γ₁ A B} → Exp {Δ₁} (Γ₁ , A) B → Exp {Δ₁} Γ₁ (A ⇒ B)
  Tlambda : ∀{Δ₁ Γ₁ T} → Exp {suc Δ₁} (ΔweakenΓ same Γ₁) T → Exp {Δ₁} Γ₁ (4all T)
  var : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁) → Exp Γ₁ (Tat icx)
  app : ∀{Δ₁ Γ₁ A B} → Exp {Δ₁} Γ₁ (A ⇒ B) → Exp Γ₁ A → Exp Γ₁ B
  appU : ∀{Δ₁ Γ₁ T} → Exp {Δ₁} Γ₁ (4all T)
    → (A : A Δ₁)
    → Exp {Δ₁} Γ₁ (ΔsubA same A T)
  Y : ∀{Δ₁ Γ₁} → Exp {Δ₁} Γ₁ 𝟚
  N : ∀{Δ₁ Γ₁} → Exp {Δ₁} Γ₁ 𝟚

data U : {Δ₁ : Δ} → Γ Δ₁ → A Δ₁ → Set
data V : {Δ₁ : Δ} → Γ Δ₁ → A Δ₁ → Set

lToType : ∀{Δ₁} → List (A Δ₁) → A Δ₁ → A Δ₁
lToType [] T = T
lToType (T₁ ∷ Ts) T₂ = T₁ ⇒ (lToType Ts T₂)

lToExps : ∀{Δ₁} → Γ Δ₁ → List (A Δ₁) → Set
lToExps Γ₁ [] = ⊤
lToExps Γ₁ (T ∷ Ts) = (V Γ₁ T) × (lToExps Γ₁ Ts)

data Γpre : ∀{Δ₁} → Γ Δ₁ → Set where
  same : ∀{Δ₁ Γ₁} → Γpre {Δ₁} Γ₁
  next : ∀{Δ₁ Γ₁ T} → Γpre {Δ₁} Γ₁ → Γpre (Γ₁ , T)

ΓweakenΓ : ∀{Δ₁ Γ₁} → Γpre {Δ₁} Γ₁ → A Δ₁ → Γ Δ₁
ΓweakenΓ (same {_} {Γ₁}) A₁ = Γ₁ , A₁
ΓweakenΓ (next {_} {_} {A₁} pre) A₂ = (ΓweakenΓ pre A₂) , A₁

ΓweakenICX : ∀{Δ₁ Γ₁} → (pre : Γpre {Δ₁} Γ₁) → (W : A Δ₁)
  → (icx : InCtx Γ₁) → Σ (InCtx (ΓweakenΓ pre W)) (λ icx' → Tat icx' ≡ Tat icx)
ΓweakenICX same W icx = next icx , refl
ΓweakenICX (next pre) W same = same , refl
ΓweakenICX (next pre) W (next icx) with ΓweakenICX pre W icx
... | (i , p) = (next i  , p)

-- in case of right output, means translate x from Γ to (ΓsubΓ icx)
varSub : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁)
  → (x : InCtx Γ₁) → (Tat icx ≡ Tat x) ⊎ (Σ (InCtx (ΓsubΓ icx)) (λ i → Tat i ≡ Tat x))
varSub same same = inj₁ refl
varSub same (next x) = inj₂ (x , refl)
varSub (next icx) same = inj₂ (same , refl)
varSub (next icx) (next x) with varSub icx x
... | inj₁ p = inj₁ p
... | inj₂ (i , p) = inj₂ (next i , p)

data U where
  varapp : ∀{Δ₁ Γ₁}
    → (Ts : List (A Δ₁))
    → {out : A Δ₁}
    → (icx : InCtx Γ₁)
    → (Tat icx ≡ lToType Ts out)
    → (lToExps Γ₁ Ts)
    → U Γ₁ out
  -- appU : ∀{Δ₁ Γ₁ T} → U {Δ₁} Γ₁ (4all T) -- TODO: does this need to be bigapp?
  --   → (A : A Δ₁)
  --   → U {Δ₁} Γ₁ (ΔsubA same A T)
    -- TODO: yes, appU needs to be bigapp. Also, maybe needs to be combined with varapp?
    -- what if I have a function f : Nat ⇒ ∀ T . T ⇒ Nat
    -- and I want to apply (f 5 Nat 7)

--------------------------------------------------------------------------------
-- TODO: for next time:
{-
  1) Temporarily remove appU - DONE
  2) figure out why Tlambda cases are harder than lambda cases.
  3) solve Tlambda cases
  4) combine app and appU into varapp, so instead of (List Type) it will need to
    work with (List (Type ⊎ ⊤)) where ⊤ represents type arguments.
-}
--------------------------------------------------------------------------------

data V where
  lambda : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {A₁ A₂ : A Δ₁}
    → V (Γ₁ , A₁) A₂ → V Γ₁ (A₁ ⇒ A₂)
  Tlambda : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {A₁ : A (suc Δ₁)}
    → V {suc Δ₁} (ΔweakenΓ same Γ₁) A₁ → V {Δ₁} Γ₁ (4all A₁)
  fromU : ∀{Δ₁ Γ₁ A₁} → U {Δ₁} Γ₁ A₁ → V Γ₁ A₁
-- IDEA: the ΔweakenΓ present in the context of Tlambda makes things more difficult.
-- If I were to combine Γ and Δ into one context, it could make things easier?
-- But if I were to do that, then in lambda, the type would have to be weakened

ΓweakenV : ∀{Δ₁ Γ₁ A₁} → (pre : Γpre Γ₁) → (W : A Δ₁)
  → V {Δ₁} Γ₁ A₁ → V (ΓweakenΓ pre W) A₁

ΓweakenVs : ∀{Δ₁ Γ₁} → (pre : Γpre Γ₁) → (W : A Δ₁)
  → (Ts : List (A Δ₁))
  → lToExps Γ₁ Ts → lToExps (ΓweakenΓ pre W) Ts
ΓweakenVs pre W [] Vs = tt
ΓweakenVs pre W (x ∷ Ts) (V , Vs) = ΓweakenV pre W V , ΓweakenVs pre W Ts Vs


-- IDEA: can I incorporoate both kinds of weakening into one function?
-- so that the induction is general enough to work?
ΓweakenV pre W (lambda v) = lambda (ΓweakenV (next pre) W v)
ΓweakenV pre W (Tlambda v) = Tlambda {! ΓweakenV (ΔweakenΓpre pre) W v  !}
ΓweakenV pre W (fromU (varapp Ts icx p Vs)) with ΓweakenICX pre W icx
... | (i , p₁) = fromU (varapp Ts i (trans p₁ p) (ΓweakenVs pre W Ts Vs))
-- ΓweakenV pre W (fromU (appU u T)) = {!   !}

ΔweakenV : ∀{Δ₁ Γ₁ A₁} → (pre : Δpre Δ₁)
  → V {Δ₁} Γ₁ A₁ → V {ΔweakenΔ pre} (ΔweakenΓ pre Γ₁) (ΔweakenA pre A₁)
ΔweakenV pre (lambda v) = lambda (ΔweakenV pre v)
ΔweakenV {Δ₁} pre (Tlambda v) = Tlambda {! ΔweakenV (next pre) v  !} -- TODO: WHY ARE THE Tlambda cases harder than lambda cases!!!!!!!!!!!!
ΔweakenV pre (fromU (varapp Ts icx p Vs)) = {!   !}
-- ΔweakenV pre (fromU (appU u T)) = {!   !}
