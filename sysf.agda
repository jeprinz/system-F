open import Data.Nat

TypeContext = ℕ

data Context : Set where
  emptyCtx : Context
  consCtx : (Γ : Context) → Type Γ → Context

data InTypeCtx : TypeContext → Set where
  end : ∀{Γ} → InTypeCtx (suc Γ)
  step : ∀{Γ} → InTypeCtx Γ → InTypeCtx (suc Γ)

data Type : TypeContext → Set where
  var : ∀{Γ} → InTypeCtx Γ → Type Γ
  4all : ∀{Γ} → Type (suc Γ) → Type Γ

-- no reason that this would be any easier than ExpAttempt3, right?
