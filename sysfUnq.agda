{-# OPTIONS --cumulativity #-}
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum
open import Data.Product

Δ = ℕ

-- same as Fin
data InTypeCtx : Δ → Set where
  end : ∀{Γ₁} → InTypeCtx (suc Γ₁)
  step : ∀{Γ₁} → InTypeCtx Γ₁ → InTypeCtx (suc Γ₁)

data Type : Δ → Set where
  var : ∀{Δ₁} → InTypeCtx Δ₁ → Type Δ₁
  4all : ∀{Δ₁} → Type (suc Δ₁) → Type Δ₁ -- TODO: build levels into this
  arrow : ∀{Δ₁} → Type Δ₁ → Type Δ₁ → Type Δ₁

data Γ : Δ → Set where
  EmptyCtx : ∀ {Δ₁} → Γ Δ₁
  ConsCtx : ∀ {Δ₁} → (Γ₁ : Γ Δ₁) → Type Δ₁ → Γ Δ₁

unqΔ : Δ → Set₁
unqΔ 0 = ⊤
unqΔ (suc Δ₁) = Σ (unqΔ Δ₁) (λ t → Set)

unqT : ∀{Δ₁} → Type Δ₁ → unqΔ Δ₁ → Set₁
unqT (var end) (_ , T) = T
unqT (var (step x)) (δ , _) = unqT (var x) δ
unqT (4all T) δ = (A : Set) → unqT T (δ , A)
unqT (arrow T T₁) δ = (unqT T δ) → (unqT T₁ δ)

unqΓ : ∀{Δ₁} → Γ Δ₁ → unqΔ Δ₁ → Set₁
unqΓ EmptyCtx δ = ⊤
unqΓ (ConsCtx Γ₁ T) δ = Σ (unqΓ Γ₁ δ) (λ _ → unqT T δ ) -- its an underscore because these are not full dependent types, it can never actually depend on previous types in context.

data Value : {Δ₁ : Δ} → (Γ₁ : Γ Δ₁) → ((δ : unqΔ Δ₁) → {- unqΓ Γ₁ δ → -} Set₁)
  → Set₁ where
  lambda : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} (ConsCtx Γ₁ A) (unqT B)
    → Value {Δ₁} Γ₁ (unqT (arrow A B))

    -- TODO: it doesn't make sense that lambda should be easy but Tlambda requires
    -- weaken. Maybe I should consolidate Δ and Γ into one, and add Type type to Type?
    -- TODO: no, but the issue is that Type needs to be weakened either way?
  Tlambda : ∀{Δ₁ Γ₁ B} → Value {suc Δ₁} Γ₁ (unqT B)
    → Value {Δ₁} {!   !} (unqT (4all B))
--   lambda : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} (ConsCtx Γ₁ A) B → Value {Δ₁} Γ₁ (arrow A B)
  -- Tlambda : ∀{Δ₁ Γ₁ T} → Value {suc Δ₁} (weakenΓ Γ₁) (weakenType T) → Value {Δ₁} Γ₁ T
--   var : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁) → Value Γ₁ (Tat icx)
--   app : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} Γ₁ (arrow A B) → Value Γ₁ A → Value Γ₁ B
--   appU : ∀{Δ₁ Γ₁ T} → Value {Δ₁} Γ₁ (4all T)
--     → (A : Type Δ₁)
--     → Value {Δ₁} Γ₁ (subType end A T)

weakenInTypeCtx : ∀{Δ₁} → InTypeCtx Δ₁ → InTypeCtx (suc Δ₁)
weakenInTypeCtx end = end
weakenInTypeCtx (step itc) = step (weakenInTypeCtx itc)

weakenType : ∀{Δ₁} → Type Δ₁ → Type (suc Δ₁)
weakenType (var x) = var (weakenInTypeCtx x)
weakenType (4all T) = 4all (weakenType T)
weakenType (arrow A B) = arrow (weakenType A) (weakenType B)

weakenΓ : ∀{Δ₁} → Γ Δ₁ → Γ (suc Δ₁)
weakenΓ EmptyCtx = EmptyCtx
weakenΓ (ConsCtx Γ₁ B) = ConsCtx (weakenΓ Γ₁) (weakenType B)

data InCtx : {Δ₁ : Δ} → Γ Δ₁ → Set where
  end : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {T : Type Δ₁} → InCtx (ConsCtx Γ₁ T)
  step : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {Next : Type Δ₁} → InCtx {Δ₁} Γ₁ → InCtx (ConsCtx Γ₁ Next)

Tat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → Type Δ₁
Tat (end {_} {_} {T}) = T
Tat (step icx) = Tat icx

-- data Value : {Δ₁ : Δ} → Γ Δ₁ → Type Δ₁ → Set where
--   lambda : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} (ConsCtx Γ₁ A) B → Value {Δ₁} Γ₁ (arrow A B)
--   fromUalue : ∀{Δ₁ Γ₁ T} → Value {Δ₁} Γ₁ T → Value {Δ₁} Γ₁ T
--   Tlambda : ∀{Δ₁ Γ₁ T} → Value {suc Δ₁} (weakenΓ Γ₁) (weakenType T) → Value {Δ₁} Γ₁ T
--   var : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁) → Value Γ₁ (Tat icx)
--   app : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} Γ₁ (arrow A B) → Value Γ₁ A → Value Γ₁ B
--   appU : ∀{Δ₁ Γ₁ T} → Value {Δ₁} Γ₁ (4all T)
--     → (A : Type Δ₁)
--     → Value {Δ₁} Γ₁ (subType end A T)
