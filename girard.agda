-- Going to implement Girard's method.
-- Thus, I will use the standard concept of defining an untyped language first
-- and then define typing as a relation.
-- In the future, I can see if it can work for the design where no untyped
-- language is defined, and in inference rules (which here are constructors)
-- are considered the terms of the language.

open import Data.Nat

-- Define the grammar:
TypeContext = ℕ

data InTypeCtx : TypeContext → Set where
  end : ∀{Γ} → InTypeCtx (suc Γ)
  step : ∀{Γ} → InTypeCtx Γ → InTypeCtx (suc Γ)

data A : TypeContext → Set where
  var : ∀{Δ} → InTypeCtx Δ → A Δ
  𝟚 : ∀{Δ} → A Δ
  _⇒_ : ∀{Δ} → A Δ → A Δ → A Δ
  ∀` : ∀{Δ} → A (suc Δ) → A Δ

data Context : TypeContext → Set where
  ∅ : ∀ {Δ} → Context Δ
  _,_ : ∀ {Δ} → (Γ : Context Δ) → A Δ → Context Δ

data InContext : (Δ : TypeContext) → Context Δ → Set where
  end : ∀{Δ Γ A} → InContext Δ (Γ , A)
  step : ∀{Δ Γ A} → InContext Δ Γ → InContext Δ (Γ , A)

getA : ∀{Δ Γ} → InContext Δ Γ → A Δ
getA (end {_} {_} {A}) = A
getA (step {_} {_} {A} i) = A

weakenInTypeCtx : ∀{TC} → InTypeCtx TC → InTypeCtx (suc TC)
weakenInTypeCtx end = end
weakenInTypeCtx (step itc) = step (weakenInTypeCtx itc)

-- Weakening principle 1 from paper. As described in paper, derived from induction
-- rather than added as a constructor.
weakenType : ∀{TC} → A TC → A (suc TC)
weakenType (var x) = var (weakenInTypeCtx x)
weakenType (∀` T) = ∀` (weakenType T)
weakenType (A ⇒ B) = (weakenType A) ⇒ (weakenType B)
weakenType 𝟚 = 𝟚

weakenΓ : ∀{TC} → Context TC → Context (suc TC)
weakenΓ ∅ = ∅
weakenΓ (Γ , B) = (weakenΓ Γ) , (weakenType B)

data M : (Δ : TypeContext) → Context Δ → Set where
  var : ∀{Δ Γ} → InContext Δ Γ → M Δ Γ
  Y : ∀{Δ Γ} → M Δ Γ
  N : ∀{Δ Γ} → M Δ Γ
  lam : ∀{Δ Γ} → (a : A Δ) → M Δ (Γ , a) → M Δ Γ
  ap : ∀{Δ Γ} → M Δ Γ → M Δ Γ → M Δ Γ
  Tlam : ∀{Δ Γ} → M (suc Δ) (weakenΓ Γ) → M Δ Γ -- Λ -- TODO: is the paper wrong here? Arg should be M, not A
  Tap : ∀{Δ Γ} → M Δ Γ → A Δ → M Δ Γ -- Ap
  -- TODO: big issue: in the above Tap, the output Δ won't be the same as the input one.

-- really just subtracts one
subTC : ∀{Δ} → InTypeCtx Δ → TypeContext
subTC {suc Δ} end = Δ
subTC {suc Δ} (step itc) = suc (subTC itc)

-- read "TC at", not "T cat"
TCat : ∀{TC} → (itc : InTypeCtx TC) → TypeContext
TCat {suc TC} end = TC
TCat {suc TC} (step itc) = TCat itc

subType : ∀{Δ} → (itc : InTypeCtx Δ)
  → (toSub : A (TCat itc)) → A Δ → A (subTC itc)
subType end toSub (var end) = toSub -- [x ↦ v]x = v
subType end toSub (var (step x)) = var x -- [x ↦ v]y = y
subType (step itc) toSub (var end) = var end -- [x ↦ v]y = y
subType (step itc) toSub (var (step x)) = weakenType (subType itc toSub (var x)) -- [x ↦ v]y = ? where x ≟ y
subType itc toSub 𝟚 = 𝟚
subType itc toSub (a₁ ⇒ a₂) = (subType itc toSub a₁) ⇒ (subType itc toSub a₂)
subType itc toSub (∀` a) = ∀` (subType (step itc) toSub a)


data _,_⊢_::_ : (Δ : TypeContext) → (Γ : Context Δ) → M Δ Γ → A Δ → Set where
  VAR : ∀{Δ Γ}
    → (icx : InContext Δ Γ)
    → Δ , Γ ⊢ (var icx) :: (getA icx)
  YES : ∀{Δ Γ} →
    Δ , Γ ⊢ Y :: 𝟚
  NO : ∀{Δ Γ} →
    Δ , Γ ⊢ N :: 𝟚
  LAM : ∀{Δ Γ a₁ a₂ m}
    → Δ , (Γ , a₁) ⊢ m :: a₂
    → Δ , Γ ⊢ (lam a₁ m) :: (a₁ ⇒ a₂)
  APP : ∀{Δ Γ a a₂ m₁ m₂}
    → Δ , Γ ⊢ m₁ :: (a₂ ⇒ a)
    → Δ , Γ ⊢ m₂ :: a₂
    → Δ , Γ ⊢ (ap m₁ m₂) :: a
  TLAM : ∀{Δ Γ a m}
    → (suc Δ) , (weakenΓ Γ) ⊢ m :: a
    → Δ , Γ ⊢ (Tlam m) :: ∀` a
  TAPP : ∀{Δ Γ m b}
    → Δ , Γ ⊢ m :: ∀` b
    → (a : A Δ)
    → Δ , Γ ⊢ Tap m a :: (subType end a b)
