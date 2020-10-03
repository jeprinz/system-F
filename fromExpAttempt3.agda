open import Relation.Binary.PropositionalEquality
open import Data.Nat

data Context : Set  -- A list of types
data Type : Context → Set
data Value : (Γ : Context) → (t : Type  Γ) → Set
data UnApp : (Γ : Context) → (t : Type  Γ) → Set

TypeContext = ℕ

data Context where -- A list of types
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context) →  Type Γ → Context

data Type where
  U : {Γ : Context} → Type Γ
  arrow : ∀ {Γ} → (A B : Type Γ) → Type Γ
  4all : ∀{Γ T} → Type (ConsCtx Γ T) → Type Γ

data _prefix_ : Context → Context → Set where
  same : {Γ : Context} → Γ prefix Γ
  step : ∀{Γ' Γ T} → (p : Γ' prefix Γ) →  Γ' prefix (ConsCtx Γ T)

data Value where
  Lambda : ∀ {Γ A B} → Value (ConsCtx Γ A) B → Value Γ (arrow A B)
  fromU : ∀ {Γ T} → UnApp Γ T → Value Γ T

subCtx : ∀ {Γ' T} → (Γ : Context) → (ConsCtx Γ' T) prefix Γ
  → (v : Value Γ' T) → Context

subType : ∀{Γ' T} → (Γ : Context) → (i : (ConsCtx Γ' T) prefix Γ)
  → (A : Type Γ) → (v : Value Γ' T) → Type (subCtx Γ i v)

subValue : ∀{Γ' T} → (Γ : Context) → (i : (ConsCtx Γ' T) prefix Γ)
  → {A : Type Γ} → (e : Value Γ A) → (v : Value Γ' T)
    → Value (subCtx Γ i v) (subType Γ i A v)

subCtx (ConsCtx Γ T) same v = Γ
subCtx (ConsCtx Γ T) (step i) v = ConsCtx (subCtx Γ i v) (subType Γ i T v)

weakenType : ∀ {n Γ ΓT} → (T : Type {n} ΓT) → ΓT prefix Γ → Type {n} Γ

prefixFact : ∀{Γ' T Γ} → (ConsCtx Γ' T) prefix Γ → Γ' prefix Γ
prefixFact same = step same
prefixFact (step p) = step (prefixFact p)

subType Γ icx U v = U
subType Γ icx (arrow A B) v =
  arrow (subType Γ icx A v) (subType (ConsCtx Γ A) (step icx) B v)
data UnApp where
  Var : ∀ {Γ ΓT T} → (i : (ConsCtx ΓT T) prefix Γ) → UnApp Γ (weakenType T (prefixFact i))
  App : ∀ {Γ} → {A B : Type Γ}
    → UnApp Γ (arrow A B) →
    (x : Value Γ A) → UnApp Γ (subType (ConsCtx Γ A) same B x)

weakenCtxStep : ∀ {Γ'} → ∀ (Γ) → (p : Γ' prefix Γ) → (toAdd : Type Γ') → Context
weakenTypeStep : ∀ {Γ' Γ} → (p : Γ' prefix Γ) → (toAdd : Type Γ')
  → Type Γ → Type (weakenCtxStep Γ p toAdd)
weakenValueStep : ∀ {Γ' Γ} → (p : Γ' prefix Γ) → (toAdd : Type Γ')
  → {T : Type Γ} → Value Γ T
  → Value (weakenCtxStep Γ p toAdd) (weakenTypeStep p toAdd T)
weakenUnAppstep : ∀ {Γ' Γ} → (p : Γ' prefix Γ) → (toAdd : Type Γ')
  → {T : Type Γ} → UnApp Γ T
  → UnApp (weakenCtxStep Γ p toAdd) (weakenTypeStep p toAdd T)

{-
weakenCtxStep calls weakenTypeStep on smaller context
weakenTypeStep calls weakenValueStep on same context
weakenValueStep calls weakenUnAppstep on same context
weakenUnAppstep calls weakenCtxStep on same context

So should work. But Agda can't figure it out.
-}

weakenCtxStep Γ same toAdd = ConsCtx Γ toAdd
weakenCtxStep (ConsCtx Γ T) (step p) toAdd
  = ConsCtx (weakenCtxStep Γ p toAdd) (weakenTypeStep p toAdd T)

weakenTypeStep p toAdd U = U
weakenTypeStep {G'} {G} p toAdd (arrow A B)
  = arrow (weakenTypeStep p toAdd A) (weakenTypeStep (step p) toAdd B)

weakenValueStep p toAdd (Lambda v) = Lambda (weakenValueStep (step p) toAdd v)
weakenValueStep p toAdd (fromU u) = fromU (weakenUnAppstep p toAdd u)

-- weakenType {n} {(ConsCtx Γ' toAdd)} {ΓT} {T} same = weakenTypeStep same toAdd T
-- weakenType {n} {(ConsCtx Γ' toAdd)} {ΓT} {T} (step i) = weakenTypeStep same toAdd (weakenType i)
weakenType T same = T
weakenType T (step {_} {_} {_} {toAdd} p) = weakenTypeStep same toAdd (weakenType T p)

-- What i really want is to make weakenInCtxStep return a dependent tuple with
-- various information in it. Unfortunately, agda doesn't have that. So instead,
-- I have to define a type that will store that information. The parameters of
-- the type are the things in the context in weakenInCtxStep that I need to refer
-- to. The arguments of the single constructor are the elements of the tuple.
-- data InCtx : ∀{nT nA Γ'} → (ΓT Γ : Context) → (T : Type {nT} ΓT)
  -- → (toAdd : Type {nA} Γ') → (p : Γ' prefix Γ) → Set where
  -- inctx : ∀{nT ΓT T Γ Γ' nA p toAdd} → ∀(ΓTsub) → ∀(Tsub)
    -- → (ConsCtx {nT} ΓTsub Tsub) prefix (weakenCtxStep Γ p toAdd) → InCtx ΓT Γ T toAdd p

data InCtx : ∀ {Γ'p Γ} → ∀(Γ'T) → ∀(T) → (p : Γ'p prefix Γ)
  → (toAdd : Type Γ'p) → (ConsCtx Γ'T T) prefix Γ → Set where
  inctx : ∀ {Γ'p Γ} → ∀{Γ'T} → ∀{T} → {p : Γ'p prefix Γ}
    → {toAdd : Type Γ'p} → {icx : (ConsCtx Γ'T T) prefix Γ}
    → ∀(ΓTsub) → ∀(Tsub) -- terms of tuple start here
    → (icxsub : (ConsCtx ΓTsub Tsub) prefix (weakenCtxStep Γ p toAdd))
    → (equivalence : weakenType Tsub (prefixFact icxsub)
      ≡ weakenTypeStep p toAdd (weakenType T (prefixFact icx)))-- and end here
    → InCtx Γ'T T p toAdd icx

-- TODO: in 0th hole below, same ends up applied to inCtx, when it should
-- be applied to T. I don't know where it goes wrong, but in the goal type
-- why would weakenTypeStep same ... make sense, that implies that toAdd
-- is going on the end of the ctx.

weakenInCtxStep : ∀ {n nT Γ'p Γ} → ∀(Γ'T) → ∀(T) → (p : Γ'p prefix Γ)
  → (toAdd : Type {n} Γ'p) → (icx : (ConsCtx {nT} Γ'T T) prefix Γ)
  → InCtx Γ'T T p toAdd icx
weakenInCtxStep Γ'T T same toAdd icx = inctx Γ'T T (step icx) refl -- toAdd on end
weakenInCtxStep Γ'T T (step p) toAdd same -- T on end
  = inctx (weakenCtxStep Γ'T p toAdd) (weakenTypeStep p toAdd T) same {!   !}
weakenInCtxStep Γ'T T (step p) toAdd (step icx) with (weakenInCtxStep Γ'T T p toAdd icx) -- recurse
... | inctx ΓTsub Tsub icxsub equivalence = inctx ΓTsub Tsub (step icxsub) {!   !}

weakenUnAppstep {_} {_} {_} {Γ} p toAdd (Var i) with weakenInCtxStep _ _ p toAdd i
... | inctx ΓTsub Tsub icxsub equivalence
  -- termination problems with the following:
  = subst (λ T → UnApp (weakenCtxStep Γ p toAdd) T) equivalence (Var icxsub)
weakenUnAppstep p toAdd (App u v) = {!    !} -- will need subType(weakenTypeStep T) = T proof. Apply to substitute in type. might need to use trick where I manually implement univalence for a specific case.
  -- = App (weakenUnAppstep p toAdd u) (weakenValueStep p toAdd v)

subValue Γ icx (Lambda e) v = Lambda (subValue _ (step icx) e v)
subValue (ConsCtx Γ' T) same {A} (fromU (Var same)) v = {!   !}
-- prove subType(weakenTypeStep T) = T for both above and below cases.
subValue (ConsCtx Γ' T) same {_} (fromU (Var (step icx))) v = {!   !} -- just return the var without substitution, fromU (Var icx)
subValue .(ConsCtx _ _) (step icx) (fromU (Var x)) v = {!   !} -- recurse on subValue
-- TODO: shouldn't sub on App case actually use eval?
subValue Γ icx (fromU (App x x₁)) v = {!   !}
