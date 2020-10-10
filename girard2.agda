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

data _Δpre_ : Δ → Δ → Set where
  same : ∀{Δ₁} → Δ₁ Δpre Δ₁
  next : ∀{Δ₁ Δ₂} → Δ₁ Δpre Δ₂ → Δ₁ Δpre (suc Δ₂)

-- Insert a new type in context at Δins, ins=insert

-- This really just adds one, but in a sufficiently typed way to
-- make subsequent things easier
ΔweakenΔ : {Δins Δ₁ : Δ} → Δins Δpre Δ₁ → Δ
ΔweakenΔ {Δins} {Δ₁} same = suc Δ₁
ΔweakenΔ (next pre) = suc (ΔweakenΔ pre)

ΔweakenITC : ∀{Δins Δ₁} → (pre : Δins Δpre Δ₁) → InTypeCtx Δ₁ → InTypeCtx (ΔweakenΔ pre)
ΔweakenITC same itc = step itc
ΔweakenITC (next pre) end = end
ΔweakenITC (next pre) (step itc) = step (ΔweakenITC pre itc)

ΔweakenA : ∀{Δins Δ₁} → (pre : Δins Δpre Δ₁) → A Δ₁ → A (ΔweakenΔ pre)
ΔweakenA pre (var x) = var (ΔweakenITC pre x)
ΔweakenA pre (4all A₁) = 4all (ΔweakenA (next pre) A₁)
ΔweakenA pre (A₁ ⇒ A₂) = (ΔweakenA pre A₁) ⇒ (ΔweakenA pre A₂)
ΔweakenA pre 𝟚 = 𝟚

ΔweakenΓ : ∀{Δins Δ₁} → (pre : Δins Δpre Δ₁) → Γ Δ₁ → Γ (ΔweakenΔ pre)
ΔweakenΓ pre EmptyCtx = EmptyCtx
ΔweakenΓ pre (ConsCtx Γ₁ A₁) = ConsCtx (ΔweakenΓ pre Γ₁) (ΔweakenA pre A₁)

data InCtx : {Δ₁ : Δ} → Γ Δ₁ → Set where
  end : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {T : A Δ₁} → InCtx (ConsCtx Γ₁ T)
  step : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → {Next : A Δ₁} → InCtx {Δ₁} Γ₁ → InCtx (ConsCtx Γ₁ Next)

ΔweakenICX : ∀{Δins Δ₁} → (pre : Δins Δpre Δ₁) → {Γ₁ : Γ Δ₁}
  → InCtx Γ₁ → InCtx (ΔweakenΓ pre Γ₁)
ΔweakenICX pre end = end
ΔweakenICX pre (step icx) = step (ΔweakenICX pre icx)

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
ΔsubA (step itc) toSub (var (step itc')) = ΔweakenA same (ΔsubA itc toSub (var itc'))
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
  -- TODO: my type for Tlambda was wrong, it didn't have a 4all in output.
  Tlambda : ∀{Δ₁ Γ₁ T} → M {suc Δ₁} (ΔweakenΓ same Γ₁) T → M {Δ₁} Γ₁ (4all T)
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

-- fact : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → ∀{icx}
--   → ΔweakenΓ same (ΓsubΓ Γ₁ icx) ≡ ΓsubΓ (ΔweakenΓ same Γ₁) (ΔweakenICX same icx)
-- fact = {!   !}

-- Need to prove various things commute

fact3 : ∀{Δ₁ Γ₁} → ∀(icx) → Tat (ΔweakenICX same icx) ≡ ΔweakenA same (Tat {Δ₁} {Γ₁} icx)
fact3 end = refl
fact3 (step icx) = fact3 icx

lemma1 : ∀{Δ₁} → {X Y Z Q : A Δ₁} → X ≡ Y → Z ≡ Q → (X ⇒ Z) ≡ (Y ⇒ Q)
lemma1 refl refl = refl

-- fact4g : ∀{Δ₁ itc} → {Γ₁ : Γ Δ₁} → (A₂ : A Δ₁) → ∀(T)
  -- → ΔsubA itc (ΔweakenA A₂) (ΔweakenA T) ≡ ΔweakenA (ΔsubA itc A₂ T)
-- fact4g = ?
-- TODO: need to generalize to above, but then need general weaken... fuck.
fact4 : ∀{Δ₁} → {Γ₁ : Γ Δ₁} → (A₂ : A Δ₁) → ∀(T)
  → ΔsubA end (ΔweakenA same A₂) (ΔweakenA same T) ≡ ΔweakenA same (ΔsubA end A₂ T)
fact4 A₂ (var x) = {!   !}
fact4 {Δ₁} {Γ₁} A₂ (4all T) = let eq = fact4 {suc Δ₁} {ΔweakenΓ same Γ₁} (ΔweakenA same A₂) T
                    in cong 4all {!   !}
fact4 {Δ₁} {Γ₁} A₂ (T₁ ⇒ T₂) = let eq1 = fact4 {Δ₁} {Γ₁} A₂ T₁
                      in let eq2 = fact4 {Δ₁} {Γ₁} A₂ T₂
                      in lemma1 eq1 eq2
fact4 A₂ 𝟚 = refl

-- subWeakComm : ∀{} →
  -- → ΔsubA

fact6 : ∀{Δins Δ₁} → {Γ₁ : Γ Δ₁} → (pre : Δins Δpre Δ₁) → ∀(A₁)
  → (ΔweakenA (next pre) (ΔweakenA same A₁)) ≡ (ΔweakenA same (ΔweakenA pre A₁))
fact6 pre (var x) = {!   !}
fact6 pre (4all A₁) = let eq = fact6 (next pre) A₁ in {!   !} -- NEED TO GENERALIZE :(
fact6 {_} {_} {Γ₁} pre (A₁ ⇒ A₂)
  = let eq1 = fact6 {_} {_} {Γ₁} pre A₁
    in let eq2 = fact6 {_} {_} {Γ₁} pre A₂
    in cong₂ (λ A₁ A₂ → A₁ ⇒ A₂) eq1 eq2
fact6 pre 𝟚 = refl

fact5 : ∀{Δins Δ₁} → {Γ₁ : Γ Δ₁} → (pre : Δins Δpre Δ₁)
  → ΔweakenΓ (next pre) (ΔweakenΓ same Γ₁) ≡ ΔweakenΓ same (ΔweakenΓ pre Γ₁)
fact5 {_} {_} {EmptyCtx} pre = refl
fact5 {_} {_} {ConsCtx Γ₁ A₁} pre
  = let eq1 = fact5 {_} {_} {Γ₁} pre
    in let eq2 = fact6 {_} {_} {Γ₁} pre A₁
    in cong₂ (λ Γ₁ A₁ → ConsCtx Γ₁ A₁) eq1 eq2


ΔweakenM : ∀{Δins Δ₁ Γ₁ A₁} → (pre : Δins Δpre Δ₁) → M {Δ₁} Γ₁ A₁
  → M (ΔweakenΓ pre Γ₁) (ΔweakenA pre A₁)
ΔweakenM pre (lambda M₁) = lambda (ΔweakenM pre M₁)
ΔweakenM pre (Tlambda {_} {_} {T} M₁) = let weakM = ΔweakenM (next pre) M₁
                            in Tlambda (subst (λ Γ' → M Γ' (ΔweakenA (next pre) T)) (fact5 pre) weakM)
ΔweakenM {Δins} {Δ₁} {Γ₁} pre (var icx) = {!   !} -- generalize fact3 and copy old case below
ΔweakenM pre (app M₁ M₂) = app (ΔweakenM pre M₁) (ΔweakenM pre M₂)
ΔweakenM {_} {_} {Γ₁} pre (appU {_} {_} {T} M₁ A₂) = let x = appU (ΔweakenM pre M₁) (ΔweakenA pre A₂)
                            in subst (λ Γ' → M (ΔweakenΓ pre Γ₁) Γ') ( {!   !} ) x -- generalize fact4 to use here
ΔweakenM pre Y = Y
ΔweakenM pre N = N
-- ΔweakenM (lambda M₁) = lambda (ΔweakenM M₁)
-- ΔweakenM (Tlambda M₁) = Tlambda (ΔweakenM M₁) -- sneaky types
-- ΔweakenM {Δ₁} {Γ₁} (var icx) = subst (λ A₁ → M (ΔweakenΓ Γ₁) A₁) (fact3 icx) (var (ΔweakenICX icx))
-- ΔweakenM (app M₁ M₂) = app (ΔweakenM M₁) (ΔweakenM M₂)
-- ΔweakenM {_} {Γ₁} {A₁} (appU {_} {_} {T} M₁ A₂)
--   = let x = appU (ΔweakenM M₁) (ΔweakenA A₂)
--     in subst (λ Γ' → M (ΔweakenΓ Γ₁) Γ') (fact4 {_} {Γ₁} A₂ T) x
-- -- ΔweakenM {_} {Γ₁} {A₁} (appU {_} {_} {T} M₁ A₂) = let x = appU (ΔweakenM M₁) (ΔweakenA A₁)
--                         -- in subst (λ Γ' → M (ΔweakenΓ Γ₁) Γ') (fact2 A₂ T) x
--                         -- TODO: maybe apply fact2 to an arg rather than whole thing?
-- ΔweakenM Y = Y
-- ΔweakenM N = N

{-

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
    -- → app (lam M₁) M₁ ↦ ΓsubM .......

data _final : ∀{Δ₁ Γ₁ A₁} → M {Δ₁} Γ₁ A₁ → Set where
  YES : ∀{Δ₁ Γ₁} → Y {Δ₁} {Γ₁} final
  NO : ∀{Δ₁ Γ₁} → N {Δ₁} {Γ₁} final

-}
