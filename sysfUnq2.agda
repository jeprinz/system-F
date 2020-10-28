{-# OPTIONS --cumulativity #-}
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum
open import Data.Product


data Γ : Set
data Type : Γ → Set
data EType : Γ → Set
data TType : Γ → Set

data Γ where
  ∅ : Γ
  _,_ : (Γ₁ : Γ) → Type Γ₁ → Γ

  -- TODO: idea: consolidate InCtx and TInCtx into a single InCtx : Γ₁ → Type Γ₁ → Set
  -- no, it already works like this, see 'T' argument below.

data TInCtx : Γ → Set

data Type where
  fromE : ∀{Γ₁} → EType Γ₁ → Type Γ₁ -- types
  fromT : ∀{Γ₁} → TType Γ₁ → Type Γ₁ -- sorts


data TType where
  U₀ : ∀{Γ₁} → TType Γ₁

data EType where
  var : ∀{Γ₁} → TInCtx Γ₁ → EType Γ₁
  4all : ∀{Γ₁} → Type (Γ₁ , fromT U₀) → EType Γ₁ -- TODO: build levels into this
  arrow : ∀{Γ₁} → Type Γ₁ → Type Γ₁ → EType Γ₁


data TInCtx where
  same : {Γ₁ : Γ} → {T : TType Γ₁} → TInCtx (Γ₁ , fromT T)
  next : {Γ₁ : Γ} → {Next : Type Γ₁} → TInCtx Γ₁ → TInCtx (Γ₁ , Next)

data InCtx : Γ → Set where
  same : {Γ₁ : Γ} → {T : EType Γ₁} → InCtx (Γ₁ , fromE T)
  next : {Γ₁ : Γ} → {Next : Type Γ₁} → InCtx Γ₁ → InCtx (Γ₁ , Next)


unqΓ : Γ → Set₁
unqT : ∀{Γ₁} → Type Γ₁ → unqΓ Γ₁ → Set₁
unqTT : ∀{Γ₁} → TType Γ₁ → unqΓ Γ₁ → Set₁
unqET : ∀{Γ₁} → EType Γ₁ → unqΓ Γ₁ → Set₁

unqΓ ∅ = ⊤
unqΓ (Γ₁ , T) = Σ (unqΓ Γ₁) (λ γ → unqT T γ )

unqT (fromE x) = unqET x
unqT (fromT x) = unqTT x

unqTT U₀ γ = Set₀

unqET (var (same {_} {U₀})) (_ , T) = T
unqET (var (next i)) (γ , _) = unqET (var i) γ
unqET (4all T) γ = (A : Set₀) → unqT T (γ , A)
unqET (arrow T T₁) γ = (unqT T γ) → (unqT T₁ γ)


Tat : ∀{Γ₁} → InCtx Γ₁ → (unqΓ Γ₁ → Set₁)
Tat (same {_} {T}) (γ , _) = unqT (fromE T) γ -- unqT T γ
Tat (next icx) (γ , _) = Tat icx γ

-- TODO: make A and B type args not implicit
data Exp : (Γ₁ : Γ) → (unqΓ Γ₁ → Set₁) → Set₁
unq : ∀{Γ₁ T} → Exp Γ₁ T → (γ : unqΓ Γ₁) → T γ

data Exp where
    -- TODO: maybe Lambda only needs to input A, and gets B from e
    -- Lambda : {Γ₁ : Γ} → (A : Type Γ₁) → (B : Type (Γ₁ , A)) →
      -- Exp (Γ₁ , A) (unqT B) → Exp Γ₁ (λ γ → ((x : unqT A γ) → unqT B (γ , x)))
    ELambda : {Γ₁ : Γ} → (A B : Type Γ₁) →
      Exp Γ₁ (unqT B) → Exp Γ₁ (unqET (arrow A B))
    Var : ∀{Γ} → (icx : InCtx Γ) → Exp Γ (λ γ → Tat icx γ)
    App : {Γ₁ : Γ} → (A : Type Γ₁) → (B : Type (Γ₁ , A)) →
        Exp Γ₁ (λ γ → (a : unqT A γ) → unqT B (γ , a))
        → (x : Exp Γ₁ (unqT A)) → Exp Γ₁ (λ γ → unqT B (γ , unq x γ))

proj : ∀{Γ₁} → (icx : InCtx Γ₁) → (γ : unqΓ Γ₁) → Tat icx γ
proj same (γ , t) = t
proj (next icx) (γ , _) = proj icx γ

-- unq (Lambda _ _ e) γ = λ x → unq e (γ , x)
unq (ELambda _ _ e) γ = λ x → unq e γ
unq (Var icx) γ = proj icx γ
unq (App _ _ e e₁) γ = (unq e γ) (unq e₁ γ)

typeOf : ∀{Γ₁ T} → Exp Γ₁ T → Type Γ₁
typeOf (ELambda A B e) = fromE (arrow A B)
typeOf (Var icx) = fromE (var {!   !})
typeOf (App A B e e₁) = B

-- idE : Exp ∅ (λ γ → (T : Set₀) → T → T)
-- idE = Lambda (fromT U₀) (fromE (arrow (fromE (var same)) (fromE (var same)))) -- λ T . λ t . t
        -- (Lambda (fromE (var same)) (fromE (var (next same))) (Var same))

Γat : ∀{Γ₁} → InCtx Γ₁ → Γ
Γat {Γ , _} same = Γ
Γat (next icx) = Γat icx

TΓat : ∀{Γ₁} → TInCtx Γ₁ → Γ
TΓat {Γ , _} same = Γ
TΓat (next icx) = TΓat icx

Tat' : ∀{Γ₁} → (icx : InCtx Γ₁) → Type (Γat icx)
Tat' {_ , T} same = T
Tat' (next icx) = Tat' icx


-- I'm going to need to define subTx and subEx, for x in the following list:
-- Γ, TType, EType, Type, InCtx, TInCtx, Exp
-- Instead of subTTinCtx and subEInCtx, I will need special cases that return toSub
-- in Type and Exp respectively.
-- subTInCtx and subETinCtx will need to have contradiction cases that can't happen


-- Type substituion

subTΓ : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx)) → Γ
subTTType : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  → TType Γ₁ → TType (subTΓ ticx toSub)
subTEType : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  → EType Γ₁ → EType (subTΓ ticx toSub)
subTType : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  → Type Γ₁ → Type (subTΓ ticx toSub)
subTInCtx : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  → InCtx Γ₁ → InCtx (subTΓ ticx toSub)
subTExp : ∀{Γ₁ T} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  → Exp Γ₁ T → Exp (subTΓ ticx toSub) {!   !} -- (unqT (subTType ticx toSub T))

-- subTΓ : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx)) → Γ
subTΓ {Γ₁ , _} same _ = Γ₁
subTΓ {Γ₁ , T} (next ticx) toSub = subTΓ ticx toSub , subTType ticx toSub T

-- subTTType : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
--   → TType Γ₁ → TType (subTΓ ticx)
subTTType ticx toSub U₀ = U₀

-- subTType : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx)) -- TODO: note this definition needs to come before subTEType
  -- → Type Γ₁ → Type (subTΓ ticx)
subTType ticx toSub (fromE T) = fromE (subTEType ticx toSub T)
subTType ticx toSub (fromT T) = fromT (subTTType ticx toSub T)
-- subTEType : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  -- → EType Γ₁ → EType (subTΓ ticx)
subTEType ticx toSub (var x) = {!   !}
subTEType ticx toSub (4all T) = 4all (subTType (next ticx) toSub T)
subTEType ticx toSub (arrow T₁ T₂) = arrow (subTType ticx toSub T₁) (subTType ticx toSub T₂)

-- subTInCtx : ∀{Γ₁} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  -- → InCtx Γ₁ → InCtx (subTΓ ticx)
-- Note that Agda can tell that same same case is impossible
subTInCtx (next ticx) toSub same = same
subTInCtx same toSub (next icx) = icx
subTInCtx (next ticx) toSub (next icx) = next (subTInCtx ticx toSub icx)

-- subTExp : ∀{Γ₁ T} → (ticx : TInCtx Γ₁) → (toSub : Type (TΓat ticx))
  -- → Exp Γ₁ (unqT T) → Exp (subTΓ ticx) (unqT (subTType ticx toSub T))
subTExp {_} {.(λ γ → unqT A γ → unqT B γ)} ticx toSub (ELambda A B e) = {!   !}
subTExp {_} {.(Tat icx)} ticx toSub (Var icx) = {!   !}
subTExp {_} {.(λ γ → unqT B (γ , unq e₁ γ))} ticx toSub (App A B e e₁) = {!   !}



-- old stuff past this line:
--------------------------------------------------------------

-- TODO: TODO: TODO: something very wrong, toSub should be an Exp right? not Type?
-- subEΓ : {Γ₁ : Γ} → (icx : InCtx Γ₁) {- → Exp (Γat icx) (unqT (Tat' icx)) -} → Γ
-- subET : {Γ₁ : Γ} → (icx : InCtx Γ₁) -- → (toSub : Exp (Γat icx) (unqT (Tat' icx)))
  -- → Type Γ₁ → Type (subEΓ icx)
-- subTICX : {Γ₁ : Γ} → (icx : InCtx Γ₁) → (toSub : Type (Γat icx))
  -- → TInCtx Γ₁ → (TInCtx (subΓ icx toSub)) ⊎ Type (subΓ icx toSub)

-- subEΓ {Γ₁ , _} same = Γ₁
-- subEΓ {Γ₁ , T} (next icx) = (subEΓ icx , subET icx T)

-- subET icx U₀ = U₀
-- subET icx (var x) = {!   !}-- TODO: problem is that this can't be a TInCtx, but can't prove it
  -- TODO: or can I prove it? try pattern matching on T arg to same
-- subET icx (4all T) = 4all (subET (next icx) T)
-- subET icx (arrow T T₁) = arrow (subET icx T) (subET icx T₁)

-- varSub : {Γ₁ : Γ} → (icx : InCtx Γ₁) → (toSub : Type (Γat icx))
  -- → TInCtx Γ₁ → (TInCtx (subΓ icx toSub)) ⊎ Exp

-- TODO: which of the two kinds of substitution (term or type) are we dealing with here,
-- and what do each of them do to types (and terms)?
-- subT icx toSub U₀ = U₀
-- subT icx toSub (var x) = {!   !}
-- ...                       | inj₁ icx' = var icx'
-- ...                       | inj₂ T = T
-- subT icx toSub (4all T) = 4all (subT (next icx) toSub T)
-- subT icx toSub (arrow T T₁) = arrow (subT icx toSub T) (subT icx toSub T₁)


-- subTICX same toSub same = inj₂ toSub
-- subTICX same toSub (next ticx) = inj₁ ticx
-- subTICX (next icx) toSub same = inj₁ same
-- subTICX (next icx) toSub (next ticx) with subTICX icx toSub ticx
-- ...                                     | inj₁ icx' = inj₁ (next icx')
-- ...                                     | inj₂ T = inj₂ {!   !}
