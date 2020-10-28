open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.List.Base
open import Data.Fin

iℕ : ℕ
iℕ = 10
Δ = List (Fin iℕ)

-- same as Fin
data InTypeCtx : Δ → Set where
  end : ∀{Γ₁ T} → InTypeCtx (T ∷ Γ₁)
  step : ∀{Γ₁ T} → InTypeCtx Γ₁ → InTypeCtx (T ∷ Γ₁)

data Type : Δ → Set where
  var : ∀{Δ₁} → InTypeCtx Δ₁ → Type Δ₁
  4all : ∀{Δ₁ T} → Type (T ∷ Δ₁) → Type Δ₁
  arrow : ∀{Δ₁} → Type Δ₁ → Type Δ₁ → Type Δ₁

data Γ : Δ → Set where
  EmptyCtx : ∀ {Δ₁} → Γ Δ₁
  ConsCtx : ∀ {Δ₁} → (Γ₁ : Γ Δ₁) → Type Δ₁ → Γ Δ₁



-- need Δpre, and more general weakening.

weakenInTypeCtx : ∀{Δ₁ T} → InTypeCtx Δ₁ → InTypeCtx (T ∷ Δ₁)
weakenInTypeCtx end = end
weakenInTypeCtx (step itc) = step (weakenInTypeCtx itc)

weakenType : ∀{Δ₁ T} → Type Δ₁ → Type (T ∷ Δ₁)
weakenType (var x) = var (weakenInTypeCtx x)
weakenType (4all T) = {!   !} -- 4all (weakenType T)
weakenType (arrow A B) = arrow (weakenType A) (weakenType B)
{-


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


data Exp : {Δ₁ : Δ} → Γ Δ₁ → Type Δ₁ → Set where
  lambda : ∀{Δ₁ Γ₁ A B} → Exp {Δ₁} (ConsCtx Γ₁ A) B → Exp {Δ₁} Γ₁ (arrow A B)
  Tlambda : ∀{Δ₁ Γ₁ T} → Exp {suc Δ₁} (weakenΓ Γ₁) (weakenType T) → Exp {Δ₁} Γ₁ T
  var : ∀{Δ₁ Γ₁} → (icx : InCtx {Δ₁} Γ₁) → Exp Γ₁ (Tat icx)
  app : ∀{Δ₁ Γ₁ A B} → Exp {Δ₁} Γ₁ (arrow A B) → Exp Γ₁ A → Exp Γ₁ B
  appU : ∀{Δ₁ Γ₁ T} → Exp {Δ₁} Γ₁ (4all T)
    → (A : Type Δ₁)
    → Exp {Δ₁} Γ₁ (subType end A T)


-- IDEA: define ctxTypeΔ : Δ → Set, and ctxTypeΓ: Γ → Set
-- also define unqT and unq
-- see if it would be possible to define parametricity on these types

-- ctxTypeΔ : Δ → Set i
-}
