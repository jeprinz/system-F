open import Data.Nat
open import Relation.Binary.PropositionalEquality

TypeContext = ℕ

-- same as Fin
data InTypeCtx : TypeContext → Set where
  end : ∀{Γ} → InTypeCtx (suc Γ)
  step : ∀{Γ} → InTypeCtx Γ → InTypeCtx (suc Γ)

data Type : TypeContext → Set where
  var : ∀{TC} → InTypeCtx TC → Type TC
  4all : ∀{TC} → Type (suc TC) → Type TC
  arrow : ∀{TC} → Type TC → Type TC → Type TC

data Context : TypeContext → Set where
  EmptyCtx : ∀ {TC} → Context TC
  ConsCtx : ∀ {TC} → (Γ : Context TC) → Type TC → Context TC

weakenInTypeCtx : ∀{TC} → InTypeCtx TC → InTypeCtx (suc TC)
weakenInTypeCtx end = end
weakenInTypeCtx (step itc) = step (weakenInTypeCtx itc)

weakenType : ∀{TC} → Type TC → Type (suc TC)
weakenType (var x) = var (weakenInTypeCtx x)
weakenType (4all T) = 4all (weakenType T)
weakenType (arrow A B) = arrow (weakenType A) (weakenType B)

weakenΓ : ∀{TC} → Context TC → Context (suc TC)
weakenΓ EmptyCtx = EmptyCtx
weakenΓ (ConsCtx Γ B) = ConsCtx (weakenΓ Γ) (weakenType B)

data InCtx : {TC : TypeContext} → Context TC → Type TC → Set where
  end : ∀{TC} → {Γ : Context TC} → {T : Type TC} → InCtx (ConsCtx Γ T) T
  step : ∀{TC T} → (Γ : Context TC) → {Next : Type TC} → InCtx {TC} Γ T → InCtx (ConsCtx Γ Next) T

-- really just subtracts one
subTC : ∀{TC} → InTypeCtx TC → TypeContext
subTC {suc TC} end = TC
subTC {suc TC} (step itc) = suc (subTC itc)

-- data _prefixTC_ : TypeContext → TypeContext → Set where
--   same : ∀{TC} → TC prefixTC TC
--   next : ∀{TC TC'} → TC prefixTC TC' → TC prefixTC (suc TC')

-- read "TC at", not "T cat"
TCat : ∀{TC} → (itc : InTypeCtx TC) → TypeContext
TCat {suc TC} end = TC
TCat {suc TC} (step itc) = TCat itc

subType : ∀{TC} → (itc : InTypeCtx TC)
  → (toSub : Type (TCat itc)) → Type TC → Type (subTC itc)
subType end toSub (var end) = toSub
subType end toSub (var (step itc')) = var itc'
subType (step itc) toSub (var end) = var end -- TODO: think what these cases actually mean!
subType (step itc) toSub (var (step itc')) = weakenType (subType itc toSub (var itc'))
subType itc toSub (4all T) = 4all (subType (step itc) toSub T)
-- subType itc (4all T) = 4all (subst (λ tc → Type tc) (fact1 itc) (subType (step itc) T))
subType itc toSub (arrow A B)
  = arrow (subType itc toSub A) (subType itc toSub B)

subContext : ∀{TC} → (itc : InTypeCtx TC)
  → (toSub : Type (TCat itc)) → Context TC → Context (subTC itc)
subContext itc toSub EmptyCtx = EmptyCtx
subContext itc toSub (ConsCtx Γ T)
  = ConsCtx (subContext itc toSub Γ) (subType itc toSub T)

data Value : {TC : TypeContext} → Context TC → Type TC → Set
data Ualue : {TC : TypeContext} → Context TC → Type TC → Set

data Value where
  lambda : ∀{TC Γ A B} → Value {TC} (ConsCtx Γ A) B → Value {TC} Γ (arrow A B)
  fromUalue : ∀{TC Γ T} → Ualue {TC} Γ T → Value {TC} Γ T
  Tlambda : ∀{TC Γ T} → Value {suc TC} (weakenΓ Γ) (weakenType T) → Value {TC} Γ T
  -- Now I need rules that correspond to 4all


data Ualue where
  var : ∀{TC Γ T} → InCtx {TC} Γ T → Ualue Γ T
  app : ∀{TC Γ A B} → Ualue {TC} Γ (arrow A B) → Value Γ A → Ualue Γ B
  appU : ∀{TC Γ T} → Ualue {TC} Γ (4all T)
    → (A : Type TC)
    → Ualue {TC} Γ (subType end A T)
