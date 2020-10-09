open import Data.Nat
open import Relation.Binary.PropositionalEquality

Δ = ℕ

-- same as Fin
data InTypeCtx : Δ → Set where
  end : ∀{Γ₁} → InTypeCtx (suc Γ₁)
  step : ∀{Γ₁} → InTypeCtx Γ₁ → InTypeCtx (suc Γ₁)

data Type : Δ → Set where
  var : ∀{Δ₁} → InTypeCtx Δ₁ → Type Δ₁
  4all : ∀{Δ₁} → Type (suc Δ₁) → Type Δ₁
  arrow : ∀{Δ₁} → Type Δ₁ → Type Δ₁ → Type Δ₁

data Γ : Δ → Set where
  EmptyCtx : ∀ {Δ₁} → Γ Δ₁
  ConsCtx : ∀ {Δ₁} → (Γ₁ : Γ Δ₁) → Type Δ₁ → Γ Δ₁

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
  → (toSub : Type (TCat itc)) → Type Δ₁ → Type (subTC itc)
subType end toSub (var end) = toSub
subType end toSub (var (step itc')) = var itc'
subType (step itc) toSub (var end) = var end -- TODO: think what these cases actually mean!
subType (step itc) toSub (var (step itc')) = weakenType (subType itc toSub (var itc'))
subType itc toSub (4all T) = 4all (subType (step itc) toSub T)
-- subType itc (4all T) = 4all (subst (λ tc → Type tc) (fact1 itc) (subType (step itc) T))
subType itc toSub (arrow A B)
  = arrow (subType itc toSub A) (subType itc toSub B)

subContext : ∀{Δ₁} → (itc : InTypeCtx Δ₁)
  → (toSub : Type (TCat itc)) → Γ Δ₁ → Γ (subTC itc)
subContext itc toSub EmptyCtx = EmptyCtx
subContext itc toSub (ConsCtx Γ₁ T)
  = ConsCtx (subContext itc toSub Γ₁) (subType itc toSub T)

Tat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → Type Δ₁
Tat (end {_} {_} {T}) = T
Tat (step icx) = Tat icx


data Value : {Δ₁ : Δ} → Γ Δ₁ → Type Δ₁ → Set
data Ualue : {Δ₁ : Δ} → Γ Δ₁ → Type Δ₁ → Set

data Value where
  lambda : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} (ConsCtx Γ₁ A) B → Value {Δ₁} Γ₁ (arrow A B)
  fromUalue : ∀{Δ₁ Γ₁ T} → Ualue {Δ₁} Γ₁ T → Value {Δ₁} Γ₁ T
  Tlambda : ∀{Δ₁ Γ₁ T} → Value {suc Δ₁} (weakenΓ Γ₁) (weakenType T) → Value {Δ₁} Γ₁ T
  -- Now I need rules that correspond to 4all

data Ualue where
  var : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁) → Ualue Γ₁ (Tat icx)
  app : ∀{Δ₁ Γ₁ A B} → Ualue {Δ₁} Γ₁ (arrow A B) → Value Γ₁ A → Ualue Γ₁ B
  appU : ∀{Δ₁ Γ₁ T} → Ualue {Δ₁} Γ₁ (4all T)
    → (A : Type Δ₁)
    → Ualue {Δ₁} Γ₁ (subType end A T)

subVContext : ∀{Δ₁} → (Γ₁ : Γ Δ₁) → (icx : InCtx Γ₁) → Γ Δ₁
subVContext (ConsCtx Γ₁ T) end = Γ₁
subVContext (ConsCtx Γ₁ T) (step icx) = ConsCtx (subVContext Γ₁ icx) T

Γat : ∀{Δ₁ Γ₁} → InCtx {Δ₁} Γ₁ → Γ Δ₁
Γat {_} {ConsCtx Γ₁ T} end = Γ₁
Γat (step itc) = Γat itc


-----------------------------------------------------------------------------------
-- After this point, now we are defining evaluation in the naive way.
-- This is not finished, but it fails Agda termination check!

-- subVValue : ∀{Δ₁ T} → {Γ₁ : Γ Δ₁} → (icx : InCtx Γ₁) → (Value (Γat icx) (Tat icx))
--   → (Value Γ₁ T) → (Value (subVContext Γ₁ icx) T)
-- subVUalue : ∀{Δ₁ T} → {Γ₁ : Γ Δ₁} → (icx : InCtx Γ₁) → (Value (Γat icx) (Tat icx))
--   → (Ualue Γ₁ T) → (Value (subVContext Γ₁ icx) T)
-- eval : ∀{Δ₁ Γ₁ A B} → Value {Δ₁} Γ₁ (arrow A B) → Value Γ₁ A → Value Γ₁ B
--
-- subVValue icx v' (lambda v) = {!   !}
-- subVValue icx v' (fromUalue u) = subVUalue icx v' u
-- subVValue icx v' (Tlambda v) = {!   !}
--
-- subVUalue icx v' (var icx₁) = {!   !}
-- subVUalue icx v' (app u v) = let v₁ = subVUalue icx v' u
--                                  v₂ = subVValue icx v' v
--                              in eval v₁ v₂
-- subVUalue icx v' (appU u A) = {!   !}
--
-- eval (lambda v₁) v₂ = subVValue end v₂ v₁
-- eval (fromUalue x) v₂ = {!   !}
-- eval (Tlambda v₁) v₂ = {!   !}
