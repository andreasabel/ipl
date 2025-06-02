{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

-- Normalization by Evaluation for Graded Call-By-Push-Value.

module GradedCBPV where

-- Imports from the Agda standard library.

open import Library hiding (_×̇_)
pattern here! = here refl

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import ProMonoid as _

-- We postulate an effect algebra, a pre-ordered monoid

postulate
  effAlg : ProMonoid lzero lzero lzero

open ProMonoid effAlg public
  renaming
    ( Carrier to Eff
    ; _∙_     to infixl 6 _+_
    ; ε       to ∅
    ; _≼_     to _≤_
    ; _≈_     to _=E_
    )

-- postulate
--   +-unitˡ : ∅ + e ≡ e
--   +-unitʳ : e + ∅ ≡ e
--   +-assoc : (e₁ + e₂) + e₃ ≡ e₁ + (e₂ + e₃)
--   +-supʳ  : sup es + e ≡ sup λ i → es i + e
--   sup-k   : sup {I = I} (λ _ → e) ≡ e

-- {-# REWRITE +-unitˡ +-unitʳ +-assoc +-supʳ sup-k #-}

-- We postulate a set of generic value types.
-- There are no operations defined on these types, thus,
-- they play the type of (universal) type variables.

postulate
  Base : Set

variable
  o : Base

-- Variants (Σ) (and records (Π), resp.) can in principle have any number of
-- constructors (fields, resp.), including infinitely one.
-- In general, the constructor (field, resp.) names are given by a set I.
-- However, I : Set would make syntax already a big type, living in Set₁.
-- To keep it in Set₀, we only consider variants (records) with finitely
-- many constructors (fields), thus, I : ℕ.
-- Branching over I is then realized as functions out of El I, where
-- El I = { i | i < I} = Fin I.

set = ℕ
El  = Fin

-- Let I range over arities (constructor/field sets) and i over
-- constructor/field names.

variable
  I : set
  i : El I

variable
  e e' e₁ e₂ e₃ : Eff
  es : El I → Eff

-- The types of CBPV are classified into value types P : Ty⁺ which we
-- refer to as positive types, and computation types N : Ty⁻ which we
-- refer to as negative types.

mutual

  -- Value types

  data Ty⁺ : Set where
    base  : (o : Base) → Ty⁺                   -- Base type.
    _×̇_   : (P₁ P₂ : Ty⁺) → Ty⁺                -- Finite product (tensor).
    Σ̇     : (I : set) (Ps : El I → Ty⁺) → Ty⁺  -- Variant (sum).
    [_]   : (e : Eff) (N : Ty⁻) → Ty⁺          -- Thunk (U).
                                               -- Remembers effects.

  -- Computation types

  data Ty⁻ : Set where
    ◇̇    : (P : Ty⁺) → Ty⁻                     -- Comp (F).
    Π̇    : (I : set) (Ns : El I → Ty⁻) → Ty⁻   -- Record (lazy product).
    _⇒̇_  : (P : Ty⁺) (N : Ty⁻) → Ty⁻           -- Function type.

-- In CBPV, a variable stands for a value.
-- Thus, environments only contain values,
-- and typing contexts only value types.

-- We use introduce syntax in an intrinsically well-typed way
-- with variables being de Bruijn indices into the typing context.
-- Thus, contexts are just lists of types.

Cxt = List Ty⁺

variable
  Γ Δ Φ            : Cxt
  J                : Cxt → Set
  P P₁ P₂ P' P′ Q  : Ty⁺
  N N₁ N₂ N' N′    : Ty⁻
  Ps               : El I → Ty⁺
  Ns               : El I → Ty⁻

-- Generic values

module _ (Var : Ty⁺ → Cxt → Set) (Comp : Eff → Ty⁻ → Cxt → Set) where

  -- Right non-invertible

  data Val' : (P : Ty⁺) (Γ : Cxt) → Set where
    var    : (x : Var P Γ)                      → Val' P Γ
    pair   : (v₁ : Val' P₁ Γ) (v₂ : Val' P₂ Γ)  → Val' (P₁ ×̇ P₂) Γ
    inj    : (i : _) (v : Val' (Ps i) Γ)        → Val' (Σ̇ I Ps) Γ
    thunk  : (t : Comp e N Γ)                   → Val' ([ e ] N) Γ

-- Terms

mutual

  Val = Val' _∈_ Comp

  data Comp (e : Eff) : (N : Ty⁻) (Γ : Cxt) → Set where
    -- introductions
    ret    : (∅≤ : ∅ ≤ e)
             (v : Val P Γ)                → Comp e (◇̇ P)    Γ
    rec    : (t : ∀ i → Comp e (Ns i) Γ)  → Comp e (Π̇ I Ns) Γ
    abs    : (t : Comp e N (P ∷ Γ))       → Comp e (P ⇒̇ N)  Γ
    -- positive eliminations
    split  : (v : Val (P₁ ×̇ P₂) Γ)  (t : Comp e N (P₂ ∷ P₁ ∷ Γ))      → Comp e N Γ
    case   : (v : Val (Σ̇ I Ps) Γ)   (t : ∀ i → Comp e N (Ps i ∷ Γ))   → Comp e N Γ
    bind   : (+≤ : e₁ + e₂ ≤ e)
             (u : Comp e₁ (◇̇ P) Γ)  (t : Comp e₂ N (P ∷ Γ))           → Comp e N Γ
    -- cut
    letv   : (v : Val P Γ)          (t : Comp e N (P ∷ Γ))            → Comp e N Γ
    -- negative eliminations
    force  : (v : Val  ([ e ] N)  Γ)                  → Comp e N      Γ
    prj    : (i : _) (t : Comp e (Π̇ I Ns) Γ)          → Comp e (Ns i) Γ
    app    : (t : Comp e (P ⇒̇ N)  Γ)   (v : Val P Γ)  → Comp e N      Γ

-- Normal forms
------------------------------------------------------------------------

-- Normal values only reference variables of base type

NVar : (P : Ty⁺) (Γ : Cxt) → Set
NVar (base o) Γ = base o ∈ Γ
NVar _ _ = ⊥

-- Negative neutrals

module _ (Val : Ty⁺ → Cxt → Set) where

  -- Right non-invertible
  -- Propagates the effect from the head variable, a thunk.

  data Ne' (e : Eff) : (N : Ty⁻) (Γ : Cxt) → Set where
    force  : (x : [ e ] N ∈ Γ)                    → Ne' e N Γ
    prj    : (i : El I) (t : Ne' e (Π̇ I Ns) Γ)    → Ne' e (Ns i) Γ
    app    : (t : Ne' e (P ⇒̇ N) Γ) (v : Val P Γ)  → Ne' e N Γ

mutual

  NVal = Val' NVar Nf
  Ne   = Ne' NVal

  -- Cover monad (generalized case tree).
  -- Collects effects from all bind nodes.

  data ⟨_⟩ (e : Eff) (J : Cxt → Set) (Γ : Cxt) : Set where
    return  : (∅≤ : ∅ ≤ e)         (j : J Γ)                          → ⟨ e ⟩ J Γ
    bind    : (+≤ : e₁ + e₂ ≤ e)
              (u : Ne e₁ (◇̇ P) Γ)  (t :      ⟨ e₂ ⟩ J       (P ∷ Γ))  → ⟨ e ⟩ J Γ
    case    : (x : Σ̇ I Ps ∈ Γ)     (t : ∀ i → ⟨ e ⟩ J    (Ps i ∷ Γ))  → ⟨ e ⟩ J Γ
    split   : (x : (P₁ ×̇ P₂) ∈ Γ)  (t :       ⟨ e ⟩ J (P₂ ∷ P₁ ∷ Γ))  → ⟨ e ⟩ J Γ

  ◇ : ∀ J e Γ → Set
  ◇ J e = ⟨ e ⟩ J

  -- syntax ◇ J e = ⟨ e ⟩ J

  -- Right invertible.

  data Nf (e : Eff) : (N : Ty⁻) (Γ : Cxt) → Set where
    -- ne only needed for negative base types
    -- ne    : let N = ◇̇ (base o) in (n : ⟨ e ⟩ (Ne e N) Γ)  → Nf e N       Γ
    -- ne    : let N = ◇̇ (base o) in
    --         (+≤ : e₁ + e₂ ≤ e) (n : ⟨ e₂ ⟩ (Ne e₁ N) Γ)  → Nf e N Γ
    ret   : (v : ⟨ e ⟩ (NVal P) Γ)                        → Nf e (◇̇ P)   Γ   -- Invoke RFoc
    rec   : (ts : ∀ i → Nf e (Ns i) Γ)                    → Nf e (Π̇ I Ns) Γ
    abs   : (t : Nf e N (P ∷ Γ))                          → Nf e (P ⇒̇ N)  Γ

-- Context-indexed sets
------------------------------------------------------------------------

PSet = (Γ : Cxt) → Set
NSet = (e : Eff) (Γ : Cxt) → Set

variable
  C A A' A₁ A₂ : PSet
  B B' B₁ B₂ : NSet
  F G As : (i : El I) → PSet
  Bs Bs' Bs₁ Bs₂ : (i : El I) → NSet

-- Constructions on PSet

1̂ : PSet
1̂ Γ = ⊤

_×̂_ : (A₁ A₂ : PSet) → PSet
(A₁ ×̂ A₂) Γ = A₁ Γ × A₂ Γ

Σ̂ : (I : set) (As : El I → PSet) → PSet
(Σ̂ I F) Γ = ∃ λ i → F i Γ

_⇒̂_ : (A₁ A₂ : PSet) → PSet
(A₁ ⇒̂ A₂) Γ = A₁ Γ → A₂ Γ

Π̂ : (I : set) (As : El I → PSet) → PSet
(Π̂ I As) Γ = ∀ i → As i Γ

⟪_⟫ : (P : Ty⁺) (A : PSet) → PSet
⟪ P ⟫ A Γ = A (P ∷ Γ)

-- Constructions on NSet

_⇒ⁿ_ : (A : PSet) (B : NSet) → NSet
(A ⇒ⁿ B) e Γ = A Γ → B e Γ

Πⁿ : (I : set) (Bs : El I → NSet) → NSet
(Πⁿ I Bs) e Γ = ∀ i → Bs i e Γ

-- Morphisms between ISets

_→̇_ : (A₁ A₂ : PSet) → Set
A₁ →̇ A₂ = ∀{Γ} → A₁ Γ → A₂ Γ

_→̈_ : (B₁ B₂ : NSet) → Set
B₁ →̈ B₂ = ∀{e Γ} → B₁ e Γ → B₂ e Γ

⟨_⊙_⟩→̇_ : (P Q R : PSet) → Set
⟨ P ⊙ Q ⟩→̇ R = ∀{Γ} → P Γ → Q Γ → R Γ

⟨_⊙_⊙_⟩→̇_ : (P Q R S : PSet) → Set
⟨ P ⊙ Q ⊙ R ⟩→̇ S = ∀{Γ} → P Γ → Q Γ → R Γ → S Γ

Map : (F : (PSet) → PSet) → Set₁
Map F = ∀{A B : PSet} (f : A →̇ B) → F A →̇ F B

Π-map : (∀ i {e} → Bs i e →̇ Bs' i e) → ∀{e} → Πⁿ I Bs e →̇ Πⁿ I Bs' e
Π-map f r i = f i (r i)

-- -- Introductions and eliminations for ×̂

-- p̂air : ⟨ A ⊙ B ⟩→̇ (A ×̂ B)
-- p̂air a b = λ

-- Monotonicity
------------------------------------------------------------------------

-- Monotonization □ is a monoidal comonad

□ : (A : PSet) → PSet
□ A Γ = ∀{Δ} (τ : Γ ⊆ Δ) → A Δ

extract : □ A →̇ A
extract a = a ⊆-refl

duplicate : □ A →̇ □ (□ A)
duplicate a τ τ′ = a (⊆-trans τ τ′)

□-map : Map □
□-map f a τ = f (a τ)

extend : (□ A →̇ C) → □ A →̇ □ C
extend f = □-map f ∘ duplicate

□-weak : □ A →̇ ⟪ P ⟫ (□ A)
□-weak a τ = a (⊆-trans (_ ∷ʳ ⊆-refl) τ)

□-weak' : □ A →̇ □ (⟪ P ⟫ A)
□-weak' a τ = a (_ ∷ʳ τ)

□-sum : Σ̂ I (□ ∘ F) →̇ □ (Σ̂ I F)
□-sum (i , a) τ = i , a τ

-- Monoidality:

□-unit : 1̂ →̇ □ 1̂
□-unit = _

□-pair : ⟨ □ A₁ ⊙ □ A₂ ⟩→̇ □ (A₁ ×̂ A₂)
□-pair a b τ = (a τ , b τ)

-- -- Strong functoriality

Map! : (F : PSet → PSet) → Set₁
Map! F = ∀{A C} → ⟨ □ (λ Γ → A Γ → C Γ) ⊙ F A ⟩→̇ F C

-- Monotonicity

Mon : (A : PSet) → Set
Mon A = A →̇ □ A

monVar : Mon (P ∈_)
monVar x τ = ⊆-lookup τ x

-- Positive ISets are monotone

□-mon : Mon (□ A)
□-mon = duplicate

1-mon : Mon 1̂
1-mon = □-unit

×-mon : Mon A₁ → Mon A₂ → Mon (A₁ ×̂ A₂)
×-mon mA mB (a , b) = □-pair (mA a) (mB b)

Σ-mon : ((i : El I) → Mon (F i)) → Mon (Σ̂ I F)
Σ-mon m (i , a) = □-sum (i , m i a)

□-intro : Mon A → (A →̇ C) → (A →̇ □ C)
□-intro mA f = □-map f ∘ mA

-- Cover monad: a strong graded monad
------------------------------------------------------------------------

join : ⟨ e₁ ⟩ (⟨ e₂ ⟩ A) →̇ ⟨ e₁ + e₂ ⟩ A
join (return ∅≤e c)  = {!c !}
join (bind ≤e u c)  = {!bind u (join c) !}
join (case x t)  = case x (join ∘ t)
join (split x c) = split x (join c)

{-
◇-map : Map ⟨ e ⟩
◇-map f (return  j) = return  (f j)
◇-map f (bind  u a) = bind  u (◇-map f a)
◇-map f (case  x t) = case  x (λ i → ◇-map f (t i))
◇-map f (split x a) = split x (◇-map f a)

◇-map! : Map! ⟨ e ⟩
◇-map! f (return  j) = return  (extract f j)
◇-map! f (bind  u a) = bind  u (◇-map! (□-weak f) a)
◇-map! f (case  x t) = case  x (λ i → ◇-map! (□-weak f) (t i))
◇-map! f (split x a) = split x (◇-map! (□-weak (□-weak f)) a)

◇-bind : A →̇ ⟨ e₂ ⟩ C → ⟨ e₁ ⟩ A →̇ ⟨ e₁ + e₂ ⟩ C
◇-bind f = join ∘ ◇-map f

◇-record : (⟨ e ⟩ ∘ Πⁿ I Bs) →̈ Πⁿ I (λ i → ⟨ e ⟩ ∘ Bs i)
◇-record c i = ◇-map (_$ i) c

◇-fun : Mon A → (⟨ e ⟩ ∘ A ⇒ⁿ B) →̈ (A ⇒ⁿ (⟨ e ⟩ ∘ B))
◇-fun mA c a = ◇-map! (λ τ f → f (mA a τ)) c

-- Monoidal functoriality

◇-pair : ⟨ □ (⟨ e₁ ⟩ A₁) ⊙ ⟨ e₂ ⟩ (□ A₂) ⟩→̇ ⟨ e₂ + e₁ ⟩ (A₁ ×̂ A₂)
◇-pair ca = join ∘ ◇-map! λ τ b → ◇-map! (λ τ′ a → a , b τ′) (ca τ)

_⋉_ = ◇-pair

□◇-pair' : ⟨ □ (⟨ e₁ ⟩ A₁) ⊙ □ (⟨ e₂ ⟩ (□ A₂)) ⟩→̇ □ (⟨ e₂ + e₁ ⟩ (A₁ ×̂ A₂))
□◇-pair' ca cb τ = ◇-pair (□-mon ca τ) (cb τ)

□◇-pair : Mon A₂ → ⟨ □ (⟨ e₁ ⟩ A₁) ⊙ □ (⟨ e₂ ⟩ A₂) ⟩→̇ □ (⟨ e₂ + e₁ ⟩ (A₁ ×̂ A₂))
□◇-pair mB ca cb τ = join $
  ◇-map! (λ τ₁ b → ◇-map! (λ τ₂ a → a , mB b τ₂) (ca (⊆-trans τ τ₁))) (cb τ)

◇□-pair' : ⟨ ⟨ e₁ ⟩ (□ A₁) ⊙ □ (⟨ e₂ ⟩ (□ A₂)) ⟩→̇ ⟨ e₁ + e₂ ⟩ (□ (A₁ ×̂ A₂))
◇□-pair' ca cb = join (◇-map! (λ τ a → ◇-map! (λ τ₁ b {_} τ₂ → a (⊆-trans τ₁ τ₂) , b τ₂) (cb τ)) ca)
  -- Without the abstraction over {_}, there is an incomprehensible error.

◇□-pair : ⟨ □ (⟨ e₁ ⟩ (□ A₁)) ⊙ ⟨ e₂ ⟩ (□ A₂) ⟩→̇ ⟨ e₂ + e₁ ⟩ (□ (A₁ ×̂ A₂))
◇□-pair ca cb = join (◇-map! (λ τ b → ◇-map! (λ τ₁ a {_} τ₂ → a τ₂ , b (⊆-trans τ₁ τ₂)) (ca τ)) cb)
  -- Without the abstraction over {_}, there is an incomprehensible error.

-- Runnability

Run : (B : NSet) → Set
Run B = ∀{e₁ e₂} → ⟨ e₁ ⟩ (B e₂) →̇ B (e₁ + e₂)

-- Negative ISets are runnable

◇-run : Run (◇ A)
◇-run = join

Π-run : (∀ i → Run (Bs i)) → Run (Πⁿ I Bs)
Π-run f c i = f i (◇-map (_$ i) c)
-- Π-run f x i = Π-map {!λ j → f j!} {!!} {!!}
-- Π-run f = {!Π-map f!} ∘ ◇-record

⇒-run : Mon A → Run B → Run (A ⇒ⁿ B)
⇒-run {B = B} mA rB f = rB ∘ ◇-fun {B = B} mA f

-- Bind for the ◇ monad

◇-elim : Run B → (A →̇ B e₂) → ⟨ e₁ ⟩ A →̇ B (e₁ + e₂)
◇-elim rB f = rB ∘ ◇-map f

◇-elim! : Run B → ⟨ □ (A ⇒̂ B e₂) ⊙ ⟨ e₁ ⟩ A ⟩→̇ B (e₁ + e₂)
◇-elim! rB f = rB ∘ ◇-map! f

◇-elim-□ : Run B → ⟨ □ (A ⇒̂ B e₂) ⊙ □ (⟨ e₁ ⟩ A) ⟩→̇ □ (B (e₁ + e₂))
◇-elim-□ {B = B} rB f c = □-map (uncurry (◇-elim! {B = B} rB)) (□-pair (□-mon f) c)

◇-elim-□-alt : Run B → ⟨ □ (A ⇒̂ B e₂) ⊙ □ (⟨ e₁ ⟩ A) ⟩→̇ □ (B (e₁ + e₂))
◇-elim-□-alt {B = B} rB f c τ = ◇-elim! {B = B} rB (□-mon f τ) (c τ)

bind! : Mon C → Run B → (C →̇ ⟨ e₁ ⟩ A) → (C →̇ (A ⇒̂ B e₂)) → C →̇ B (e₁ + e₂)
bind! {B = B} mC rB f k γ = ◇-elim! {B = B} rB (λ τ a → k (mC γ τ) a) (f γ)

-- Type interpretation
------------------------------------------------------------------------

mutual
  ⟦_⟧⁺ : Ty⁺ → PSet
  ⟦ base o  ⟧⁺ = base o ∈_
  ⟦ P₁ ×̇ P₂ ⟧⁺ = ⟦ P₁ ⟧⁺ ×̂ ⟦ P₂ ⟧⁺
  ⟦ Σ̇ I P   ⟧⁺ = Σ̂ I λ i → ⟦ P i ⟧⁺
  ⟦ [ e ] N ⟧⁺ = □ (⟦ N ⟧⁻ e)

  ⟦_⟧⁻ : Ty⁻ → NSet
  ⟦ ◇̇ P   ⟧⁻ = ◇ ⟦ P ⟧⁺
  ⟦ Π̇ I N ⟧⁻ = Πⁿ I λ i → ⟦ N i ⟧⁻
  ⟦ P ⇒̇ N ⟧⁻ = ⟦ P ⟧⁺ ⇒ⁿ ⟦ N ⟧⁻

⟦_⟧ᶜ : Cxt → PSet
⟦_⟧ᶜ Γ Δ = All (λ P → ⟦ P ⟧⁺ Δ) Γ

-- ⟦ []    ⟧ᶜ = 1̂
-- ⟦ P ∷ Γ ⟧ᶜ = ⟦ Γ ⟧ᶜ ×̂ ⟦ P ⟧⁺

-- Positive types are monotone.

mon⁺ : (P : Ty⁺) → Mon ⟦ P ⟧⁺
mon⁺ (base o)  = monVar
mon⁺ (P₁ ×̇ P₂) = ×-mon (mon⁺ P₁) (mon⁺ P₂)
mon⁺ (Σ̇ I P)   = Σ-mon (mon⁺ ∘ P)
mon⁺ ([ e ] N) = □-mon

monᶜ : (Γ : Cxt) → Mon ⟦ Γ ⟧ᶜ
monᶜ Γ γ τ = All.map (λ {P} v → mon⁺ P v τ) γ

-- Negative types are runnable.

run⁻ : (N : Ty⁻) → Run ⟦ N ⟧⁻
run⁻ (◇̇ P)   = ◇-run
run⁻ (Π̇ I N) = Π-run (run⁻ ∘ N)
run⁻ (P ⇒̇ N) = ⇒-run {B = ⟦ N ⟧⁻} (mon⁺ P) (run⁻ N)

-- monᶜ []      = 1-mon
-- monᶜ (P ∷ Γ) = ×-mon (monᶜ Γ) (mon⁺ P)

-- Interpretation
------------------------------------------------------------------------

mutual

  ⦅_⦆⁺ : Val P Γ → ⟦ Γ ⟧ᶜ →̇ ⟦ P ⟧⁺
  ⦅ var x ⦆⁺      = λ γ → All.lookup γ x
  ⦅ pair v₁ v₂ ⦆⁺ = < ⦅ v₁ ⦆⁺ , ⦅ v₂ ⦆⁺ >
  ⦅ inj i v ⦆⁺    = (i ,_) ∘ ⦅ v ⦆⁺
  ⦅ thunk t ⦆⁺    = □-intro (monᶜ _) ⦅ t ⦆⁻

  λ⦅_⦆⁻ : Comp e N (P ∷ Γ) → ⟦ Γ ⟧ᶜ →̇ ⟦ P ⇒̇ N ⟧⁻ e
  λ⦅ t ⦆⁻ γ a = ⦅ t ⦆⁻ (a ∷ γ)

  ⦅_⦆⁻ : Comp e N Γ → ⟦ Γ ⟧ᶜ →̇ ⟦ N ⟧⁻ e
  ⦅ ret v ⦆⁻ = return ∘ ⦅ v ⦆⁺
  ⦅ rec t ⦆⁻ = flip λ i → {! ⦅ t i ⦆⁻ !}  -- need effect subsumption es i ≤ sup es
  ⦅ abs t ⦆⁻ = λ⦅ t ⦆⁻
  ⦅ split v t ⦆⁻ γ = let (a₁ , a₂) = ⦅ v ⦆⁺ γ in ⦅ t ⦆⁻ (a₂ ∷ (a₁ ∷ γ))
  ⦅ case v t ⦆⁻  γ = let (i , a) = ⦅ v ⦆⁺ γ in  {! ⦅ t i ⦆⁻ (a ∷ γ) !}  -- eff sub
  ⦅ bind {Γ = Γ} {N = N} t t₁ ⦆⁻ = bind! {B = ⟦ N ⟧⁻} (monᶜ Γ) (run⁻ N) ⦅ t ⦆⁻ λ⦅ t₁ ⦆⁻
  ⦅ force v ⦆⁻  = extract ∘ ⦅ v ⦆⁺
  ⦅ prj i t ⦆⁻  = (_$ i) ∘ ⦅ t ⦆⁻
  ⦅ app t v ⦆⁻  = ⦅ t ⦆⁻  ˢ ⦅ v ⦆⁺
  ⦅ letv v t ⦆⁻ = λ⦅ t ⦆⁻ ˢ ⦅ v ⦆⁺

-- Reflection and reification

mutual

  fresh□◇□ : ∀ P {Γ} → ⟪ P ⟫ (□ (⟨ ∅ ⟩ (□ ⟦ P ⟧⁺))) Γ
  fresh□◇□ P = reflect⁺□ P ∘ monVar here!

  fresh□ : ∀ P {Γ} → ⟪ P ⟫ (□ (⟨ ∅ ⟩ ⟦ P ⟧⁺)) Γ
  fresh□ P = ◇-map extract ∘ reflect⁺□ P ∘ monVar here!
  fresh□ P = reflect⁺ P ∘ monVar here!

  fresh : ∀ {P Γ} → ⟪ P ⟫ (⟨ ∅ ⟩ ⟦ P ⟧⁺) Γ
  fresh {P} = ◇-map extract (reflect⁺□ P here!)
  fresh {P} = reflect⁺ P here!

  fresh◇ : ∀ {P Γ} → ⟪ P ⟫ (⟨ ∅ ⟩ (□ ⟦ P ⟧⁺)) Γ
  fresh◇ {P} = reflect⁺□ P here!
  fresh◇ {P} = ◇-map (mon⁺ P) fresh

  -- saves us use of Mon P in freshᶜ
  reflect⁺□ : (P : Ty⁺) → (P ∈_) →̇ (⟨ ∅ ⟩ (□ ⟦ P ⟧⁺))
  reflect⁺□ (base o)  x = return (monVar x)
  reflect⁺□ (P₁ ×̇ P₂) x = split x (◇□-pair (reflect⁺□ P₁ ∘ monVar (there here!)) fresh◇)
  reflect⁺□ (Σ̇ I Ps)  x = case x λ i → ◇-map (□-map (i ,_)) fresh◇
  reflect⁺□ ([ e ] N) x = return (□-mon (reflect⁻ N ∘ force ∘ monVar x))

  reflect⁺ : (P : Ty⁺) → (P ∈_) →̇ (⟨ ∅ ⟩ ⟦ P ⟧⁺)
  reflect⁺ (base o)  x = return x
  reflect⁺ (P₁ ×̇ P₂) x = split x (□-weak (fresh□ P₁) ⋉ fresh◇)
  reflect⁺ (Σ̇ I Ps)  x = case x λ i → ◇-map (i ,_) fresh
  reflect⁺ ([ e ] N) x = return λ τ → reflect⁻ N (force (monVar x τ))

  reflect⁻ : (N : Ty⁻) → Ne e N →̇ ⟦ N ⟧⁻ e
  reflect⁻ (◇̇ P)    u = bind u fresh
  reflect⁻ (Π̇ I Ns) u = λ i → reflect⁻ (Ns i) (prj i u)
  reflect⁻ (P ⇒̇ N)  u = λ a → reflect⁻ N (app u (reify⁺ P a))

  reify⁺ : (P : Ty⁺) → ⟦ P ⟧⁺ →̇ NVal P
  reify⁺ (base o) = var
  reify⁺ (P₁ ×̇ P₂) (a₁ , a₂) = pair (reify⁺ P₁ a₁) (reify⁺ P₂ a₂)
  reify⁺ (Σ̇ I Ps)  (i  , a ) = inj i (reify⁺ (Ps i) a)
  reify⁺ ([ e ] N) a = thunk (reify⁻ N a)

  reify⁻ : (N : Ty⁻) → □ (⟦ N ⟧⁻ e) →̇ Nf e N
  reify⁻         (◇̇ P)    f = ret (◇-map (reify⁺ P) (extract f))
  reify⁻ {e = e} (Π̇ I Ns) f = rec {es = λ i → e} λ i → reify⁻ (Ns i) (□-map (_$ i) f)
  reify⁻         (P ⇒̇ N)  f = abs $ reify⁻ N $ ◇-elim-□ {B = ⟦ N ⟧⁻} (run⁻ N) (□-weak f) $ fresh□ P

ext : (⟦ Γ ⟧ᶜ ×̂ ⟦ P ⟧⁺) →̇ ⟦ P ∷ Γ ⟧ᶜ
ext (γ , a) = a ∷ γ

◇-ext : ⟨ e ⟩ (⟦ Γ ⟧ᶜ ×̂ ⟦ P ⟧⁺) →̇ ⟨ e ⟩ ⟦ P ∷ Γ ⟧ᶜ
◇-ext = ◇-map ext

-- Without the use of ◇-mon!

freshᶜ : (Γ : Cxt) → □ (⟨ ∅ ⟩ ⟦ Γ ⟧ᶜ) Γ
freshᶜ []      = λ τ → return []
freshᶜ (P ∷ Γ) = ◇-ext ∘ □◇-pair' (□-weak (freshᶜ Γ)) (fresh□◇□ P)
freshᶜ (P ∷ Γ) = ◇-ext ∘ □◇-pair (mon⁺ P) (□-weak (freshᶜ Γ)) (fresh□ P)
freshᶜ (P ∷ Γ) = ◇-ext ∘ □◇-pair' (□-weak (freshᶜ Γ)) (◇-map (mon⁺ P) ∘ (fresh□ P))
freshᶜ (P ∷ Γ) = ◇-ext ∘ λ τ →
  (□-weak (□-mon (freshᶜ Γ)) τ)
  ⋉ ◇-map (mon⁺ P) (fresh□ P τ)

norm : Comp e N →̇ Nf e N
norm {N = N} {Γ = Γ} t = reify⁻ N $ □-map (run⁻ N ∘ ◇-map ⦅ t ⦆⁻) $ freshᶜ Γ
norm {N = N} {Γ = Γ} t = reify⁻ N $ run⁻ N ∘ ◇-map ⦅ t ⦆⁻ ∘ freshᶜ Γ

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
