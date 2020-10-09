open import Data.Nat
open import Relation.Binary.PropositionalEquality

Δ = ℕ

-- same as Fin
data InTypeCtx : Δ → Set where
  end : ∀{Γ₁} → InTypeCtx (suc Γ₁)
  step : ∀{Γ₁} → InTypeCtx Γ₁ → InTypeCtx (suc Γ₁)

data A : Δ → Set where
  var : ∀{Δ₁} → InTypeCtx Δ₁ → A Δ₁
  4all : ∀{Δ₁} → A (suc Δ₁) → A Δ₁
  _⇒_ : ∀{Δ₁} → A Δ₁ → A Δ₁ → A Δ₁
  𝟚 : ∀{Δ₁} → A Δ₁

data Γ : Δ → Set where
  EmptyCtx : ∀ {Δ₁} → Γ Δ₁
  ConsCtx : ∀ {Δ₁} → (Γ₁ : Γ Δ₁) → A Δ₁ → Γ Δ₁

ΔweakenITC : ∀{Δ₁} → InTypeCtx Δ₁ → InTypeCtx (suc Δ₁)
ΔweakenITC end = end
ΔweakenITC (step itc) = step (ΔweakenITC itc)

ΔweakenA : ∀{Δ₁} → A Δ₁ → A (suc Δ₁)
ΔweakenA (var x) = var (ΔweakenITC x)
ΔweakenA (4all T) = 4all (ΔweakenA T)
ΔweakenA (A ⇒ B) = (ΔweakenA A) ⇒ (ΔweakenA B)
ΔweakenA 𝟚 = 𝟚

ΔweakenΓ : ∀{Δ₁} → Γ Δ₁ → Γ (suc Δ₁)
ΔweakenΓ EmptyCtx = EmptyCtx
ΔweakenΓ (ConsCtx Γ₁ B) = ConsCtx (ΔweakenΓ Γ₁) (ΔweakenA B)

data InCtx : {Δ₁ : Δ} → Γ Δ₁ → Set where
  end : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {T : A Δ₁} → InCtx (ConsCtx Γ₁ T)
  step : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {Next : A Δ₁} → InCtx {Δ₁} Γ₁ → InCtx (ConsCtx Γ₁ Next)

ΔweakenICX : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → InCtx Γ₁ → InCtx (ΔweakenΓ Γ₁)
ΔweakenICX end = end
ΔweakenICX (step icx) = step (ΔweakenICX icx)

-- really just subtracts one
subTC : ∀{Δ₁} → InTypeCtx Δ₁ → Δ
subTC {suc Δ₁} end = Δ₁
subTC {suc Δ₁} (step itc) = suc (subTC itc)

-- data _prefixTC_ : Δ → Δ → Set where
--   same : ∀{Δ₁} → Δ₁ prefixTC Δ₁
--   next : ∀{Δ₁ Δ₁'} → Δ₁ prefixTC Δ₁' → Δ₁ prefixTC (suc Δ₁')

-- read "Δ₁ at", not "T cat"
TCat : ∀{Δ₁} → (itc : InTypeCtx Δ₁) → Δ
TCat {suc Δ₁} end = Δ₁
TCat {suc Δ₁} (step itc) = TCat itc

subType : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : A (TCat itc)) → A Δ₁ → A (subTC itc)
subType end toSub (var end) = toSub
subType end toSub (var (step itc')) = var itc'
subType (step itc) toSub (var end) = var end
subType (step itc) toSub (var (step itc')) = ΔweakenA (subType itc toSub (var itc'))
subType itc toSub (4all T) = 4all (subType (step itc) toSub T)
subType itc toSub (A ⇒ B)
  = (subType itc toSub A) ⇒ (subType itc toSub B)
subType itc toSub 𝟚 = 𝟚

subContext : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : A (TCat itc)) → Γ Δ₁ → Γ (subTC itc)
subContext itc toSub EmptyCtx = EmptyCtx
subContext itc toSub (ConsCtx Γ₁ T)
  = ConsCtx (subContext itc toSub Γ₁) (subType itc toSub T)

Tat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → A Δ₁
Tat (end {_} {_} {T}) = T
Tat (step icx) = Tat icx


data M : {Δ₁ : Δ} → Γ Δ₁ → A Δ₁ → Set where
  lambda : ∀{Δ₁ Γ₁ A B} → M {Δ₁} (ConsCtx Γ₁ A) B → M {Δ₁} Γ₁ (A ⇒ B)
  Tlambda : ∀{Δ₁ Γ₁ T} → M {suc Δ₁} (ΔweakenΓ Γ₁) (ΔweakenA T) → M {Δ₁} Γ₁ T
  var : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁) → M Γ₁ (Tat icx)
  app : ∀{Δ₁ Γ₁ A B} → M {Δ₁} Γ₁ (A ⇒ B) → M Γ₁ A → M Γ₁ B
  appU : ∀{Δ₁ Γ₁ T} → M {Δ₁} Γ₁ (4all T)
    → (A : A Δ₁)
    → M {Δ₁} Γ₁ (subType end A T)
  Y : ∀{Δ₁ Γ₁} → M {Δ₁} Γ₁ 𝟚
  N : ∀{Δ₁ Γ₁} → M {Δ₁} Γ₁ 𝟚

ΔweakenM : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → M (ΔweakenΓ Γ₁) (ΔweakenA A₁)
ΔweakenM (lambda M₁) = lambda (ΔweakenM M₁)
ΔweakenM (Tlambda M₁) = Tlambda (ΔweakenM M₁) -- sneaky types
ΔweakenM (var icx) = {!   !}
ΔweakenM (app M₁ M₂) = app (ΔweakenM M₁) (ΔweakenM M₂)
ΔweakenM (appU M₁ A₁) = appU (ΔweakenM M₁) (ΔweakenA A₁)
ΔweakenM Y = Y
ΔweakenM N = N

subVContext : ∀{Δ₁} → (Γ₁ : Γ Δ₁) → (icx : InCtx Γ₁) → Γ Δ₁
subVContext (ConsCtx Γ₁ T) end = Γ₁
subVContext (ConsCtx Γ₁ T) (step icx) = ConsCtx (subVContext Γ₁ icx) T

Γat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → Γ Δ₁
Γat {_} {ConsCtx Γ₁ T} end = Γ₁
Γat (step itc) = Γat itc

fact : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → ∀{icx}
  → ΔweakenΓ (subVContext Γ₁ icx) ≡ subVContext (ΔweakenΓ Γ₁) (ΔweakenICX icx)
fact = {!   !}

sub : ∀{Δ₁ T} → {Γ₁ : Γ Δ₁} → (icx : InCtx Γ₁) → (M (Γat icx) (Tat icx))
  → (M Γ₁ T) → (M (subVContext Γ₁ icx) T)
sub icx M₁ (lambda M₂) = lambda (sub (step icx) M₁ M₂)
sub {Δ₁} {T} {Γ₁} icx M₁ (Tlambda M₂) -- = Tlambda {!   !}
  = let x = (sub {suc Δ₁} {ΔweakenA T} {ΔweakenΓ Γ₁} (ΔweakenICX icx) {!   !} {!   !})
    in (Tlambda {!   !} )
sub icx M₁ (var icx₁) = {!   !}
sub icx M₁ (app M₂ M₃) = app (sub icx M₁ M₂) (sub icx M₁ M₃)
sub icx M₁ (appU M₂ A₁) = {!   !}
sub icx M₁ Y = Y
sub icx M₁ N = N

-- Dynamics:

data _↦_ : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → M {Δ₁} Γ₁ A₁ → Set where
  APP : ∀{Δ₁ Γ₁ A₁ A₂ M₁' M₂} → {M₁ : M {Δ₁} Γ₁ (A₁ ⇒ A₂)}
      → M₁ ↦ M₁'
      ----------------------------
      → app M₁ M₂ ↦ app M₁' M₂
  -- APP-LAM : ∀{}
    -- → app (lam M₁) M₁ ↦ sub

data _final : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → Set where
  YES : ∀{Δ₁ Γ₁} → Y {Δ₁} {Γ₁} final
  NO : ∀{Δ₁ Γ₁} → N {Δ₁} {Γ₁} final
