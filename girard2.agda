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
ΔsubΔ : ∀{Δ₁} → InTypeCtx Δ₁ → Δ
ΔsubΔ {suc Δ₁} end = Δ₁
ΔsubΔ {suc Δ₁} (step itc) = suc (ΔsubΔ itc)

-- data _prefixTC_ : Δ → Δ → Set where
--   same : ∀{Δ₁} → Δ₁ prefixTC Δ₁
--   next : ∀{Δ₁ Δ₁'} → Δ₁ prefixTC Δ₁' → Δ₁ prefixTC (suc Δ₁')

Δat : ∀{Δ₁} → (itc : InTypeCtx Δ₁) → Δ
Δat {suc Δ₁} end = Δ₁
Δat {suc Δ₁} (step itc) = Δat itc

ΔsubA : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : A (Δat itc)) → A Δ₁ → A (ΔsubΔ itc)
ΔsubA end toSub (var end) = toSub
ΔsubA end toSub (var (step itc')) = var itc'
ΔsubA (step itc) toSub (var end) = var end
ΔsubA (step itc) toSub (var (step itc')) = ΔweakenA (ΔsubA itc toSub (var itc'))
ΔsubA itc toSub (4all T) = 4all (ΔsubA (step itc) toSub T)
ΔsubA itc toSub (A ⇒ B)
  = (ΔsubA itc toSub A) ⇒ (ΔsubA itc toSub B)
ΔsubA itc toSub 𝟚 = 𝟚

ΔsubΓ : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : A (Δat itc)) → Γ Δ₁ → Γ (ΔsubΔ itc)
ΔsubΓ itc toSub EmptyCtx = EmptyCtx
ΔsubΓ itc toSub (ConsCtx Γ₁ T)
  = ConsCtx (ΔsubΓ itc toSub Γ₁) (ΔsubA itc toSub T)

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
    → M {Δ₁} Γ₁ (ΔsubA end A T)
  Y : ∀{Δ₁ Γ₁} → M {Δ₁} Γ₁ 𝟚
  N : ∀{Δ₁ Γ₁} → M {Δ₁} Γ₁ 𝟚

ΓsubΓ : ∀{Δ₁} → (Γ₁ : Γ Δ₁) → (icx : InCtx Γ₁) → Γ Δ₁
ΓsubΓ (ConsCtx Γ₁ T) end = Γ₁
ΓsubΓ (ConsCtx Γ₁ T) (step icx) = ConsCtx (ΓsubΓ Γ₁ icx) T

fact : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → ∀{icx}
  → ΔweakenΓ (ΓsubΓ Γ₁ icx) ≡ ΓsubΓ (ΔweakenΓ Γ₁) (ΔweakenICX icx)
fact = {!   !}

-- Need to prove various things commute

fact2 : ∀{Δ₁} → (A₂ : A Δ₁) → ∀(T)
    → (ΔsubA end (ΔweakenA (ΔsubA end A₂ T)) (ΔweakenA T)) ≡ (ΔweakenA (ΔsubA end A₂ T))
fact2 A₂ T = {!   !}

fact3 : ∀{Δ₁ Γ₁} → ∀(icx) → Tat (ΔweakenICX icx) ≡ ΔweakenA (Tat {Δ₁} {Γ₁} icx)
fact3 end = refl
fact3 (step icx) = fact3 icx

ΔweakenM : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → M (ΔweakenΓ Γ₁) (ΔweakenA A₁)
ΔweakenM (lambda M₁) = lambda (ΔweakenM M₁)
ΔweakenM (Tlambda M₁) = Tlambda (ΔweakenM M₁) -- sneaky types
ΔweakenM {Δ₁} {Γ₁} (var icx) = subst (λ A₁ → M (ΔweakenΓ Γ₁) A₁) (fact3 icx) (var (ΔweakenICX icx))
ΔweakenM (app M₁ M₂) = app (ΔweakenM M₁) (ΔweakenM M₂)
ΔweakenM {_} {Γ₁} {A₁} (appU {_} {_} {T} M₁ A₂) = let x = appU (ΔweakenM M₁) (ΔweakenA A₁)
                        in subst (λ Γ' → M (ΔweakenΓ Γ₁) Γ') (fact2 A₂ T) x
                        -- TODO: maybe apply fact2 to an arg rather than whole thing?
ΔweakenM Y = Y
ΔweakenM N = N

Γat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → Γ Δ₁
Γat {_} {ConsCtx Γ₁ T} end = Γ₁
Γat (step itc) = Γat itc

ΓsubM : ∀{Δ₁ T} → {Γ₁ : Γ Δ₁} → (icx : InCtx Γ₁) → (M (Γat icx) (Tat icx))
  → (M Γ₁ T) → (M (ΓsubΓ Γ₁ icx) T)
ΓsubM icx M₁ (lambda M₂) = lambda (ΓsubM (step icx) M₁ M₂)
ΓsubM {Δ₁} {T} {Γ₁} icx M₁ (Tlambda M₂) -- = Tlambda {!   !}
  = let x = (ΓsubM {suc Δ₁} {ΔweakenA T} {ΔweakenΓ Γ₁} (ΔweakenICX icx) {!   !} {!   !})
    in (Tlambda {!   !} )
ΓsubM icx M₁ (var icx₁) = {!   !}
ΓsubM icx M₁ (app M₂ M₃) = app (ΓsubM icx M₁ M₂) (ΓsubM icx M₁ M₃)
ΓsubM icx M₁ (appU M₂ A₁) = {!   !}
ΓsubM icx M₁ Y = Y
ΓsubM icx M₁ N = N

-- Dynamics:

data _↦_ : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → M {Δ₁} Γ₁ A₁ → Set where
  APP : ∀{Δ₁ Γ₁ A₁ A₂ M₁' M₂} → {M₁ : M {Δ₁} Γ₁ (A₁ ⇒ A₂)}
      → M₁ ↦ M₁'
      ----------------------------
      → app M₁ M₂ ↦ app M₁' M₂
  -- APP-LAM : ∀{}
    -- → app (lam M₁) M₁ ↦ ΓsubM

data _final : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → Set where
  YES : ∀{Δ₁ Γ₁} → Y {Δ₁} {Γ₁} final
  NO : ∀{Δ₁ Γ₁} → N {Δ₁} {Γ₁} final
