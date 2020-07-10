{-# OPTIONS --rewriting #-}
-- {-# OPTIONS --confluence-check #-}

-- Formulæ and hypotheses (contexts)

open import Library

module Formulas (Base : Set) where

-- Propositional formulas

data Form : Set where
  Atom : (P : Base) → Form
  True False : Form
  _∨_ _∧_ _⇒_ : (A B : Form) → Form

infixl 8 _∧_
infixl 7 _∨_
infixr 6 _⇒_
infixr 5 ¬_

¬_ : (A : Form) → Form
¬ A = A ⇒ False

-- Contexts

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form) → Cxt

infixl 4 _∙_

-- Context extension (thinning)

infix 3 _≤_

data _≤_ : (Γ Δ : Cxt) → Set where
  ε    : ε ≤ ε
  weak : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

id≤ : ∀{Γ} → Γ ≤ Γ
id≤ {ε}     = ε
id≤ {Γ ∙ A} = lift id≤

-- Category of thinnings

_•_ : ∀{Γ Δ Φ} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) → Γ ≤ Φ
ε      • σ = σ
weak τ • σ = weak (τ • σ)
lift τ • weak σ = weak (τ • σ)
lift τ • lift σ = lift (τ • σ)

•-id-l : ∀{Γ Δ} (τ : Γ ≤ Δ) → id≤ • τ  ≡ τ
•-id-l ε = refl
•-id-l (weak τ) = cong weak (•-id-l τ)
•-id-l (lift τ) = cong lift (•-id-l τ)

•-id-r : ∀{Γ Δ} (τ : Γ ≤ Δ) → τ • id≤ ≡ τ
•-id-r ε = refl
•-id-r (weak τ) = cong weak (•-id-r τ)
•-id-r (lift τ) = cong lift (•-id-r τ)

•-ε-r : ∀{Γ} (τ : Γ ≤ ε) → τ • ε ≡ τ
•-ε-r ε = refl
•-ε-r (weak τ) = cong weak (•-ε-r τ)

{-# REWRITE •-id-l •-id-r •-ε-r #-}

-- Pullbacks

record RawPullback {Γ Δ₁ Δ₂} (τ₁ : Δ₁ ≤ Γ) (τ₂ : Δ₂ ≤ Γ) : Set where
  constructor rawPullback; field
    {Γ'} : Cxt
    τ₁' : Γ' ≤ Δ₁
    τ₂' : Γ' ≤ Δ₂
    comm : τ₁' • τ₁ ≡ τ₂' • τ₂

-- The glb is only unique up to isomorphism:
-- for glb (weak τ₁) (weak τ₂) we have two choices how to proceed.

glb : ∀ {Γ Δ₁ Δ₂} (τ₁ : Δ₁ ≤ Γ) (τ₂ : Δ₂ ≤ Γ) → RawPullback τ₁ τ₂
glb ε τ₂ = rawPullback τ₂ id≤ refl  -- REWRITE (•-id-r τ₂)
glb τ₁ ε = rawPullback id≤ τ₁ refl  -- REWRITE (•-id-l τ₁)
glb (weak τ₁) τ₂ =
  let rawPullback τ₁' τ₂' comm = glb τ₁ τ₂
  in  rawPullback (lift τ₁') (weak τ₂') (cong weak comm)
glb τ₁ (weak τ₂) =
  let rawPullback τ₁' τ₂' comm = glb τ₁ τ₂
  in  rawPullback (weak τ₁') (lift τ₂') (cong weak comm)
glb (lift τ₁) (lift τ₂) =
  let rawPullback τ₁' τ₂' comm = glb τ₁ τ₂
  in  rawPullback (lift τ₁') (lift τ₂') (cong lift comm)

-- glb (weak τ₁) (weak τ₂) =
--   let rawPullback τ₁' τ₂' comm = glb τ₁ τ₂
--   in  rawPullback (weak (lift τ₁')) (lift (weak τ₂')) (cong (weak ∘ weak) comm)
--   -- Here is a choice: it would also work the other way round:
--   -- rawPullback (lift (weak τ₁')) (weak (lift τ₂')) (cong (weak ∘ weak) comm)
-- glb (weak τ₁) (lift τ₂) =
--   let rawPullback τ₁' τ₂' comm = glb τ₁ (lift τ₂)
--   in  rawPullback (lift τ₁') (weak τ₂') (cong weak comm)

record WeakPullback {Γ Δ₁ Δ₂} (τ₁ : Δ₁ ≤ Γ) (τ₂ : Δ₂ ≤ Γ) : Set where
  constructor weakPullback
  field
    rawpullback : RawPullback τ₁ τ₂
  open RawPullback rawpullback public
  -- field
    -- largest : ∀ (pb : RawPullback τ₁ τ₂)

-- There are actually no pullbacks in the OPE category

-- Hypotheses

data Hyp (A : Form) : (Γ : Cxt) → Set where
  top : ∀{Γ} → Hyp A (Γ ∙ A)
  pop : ∀{Γ B} (x : Hyp A Γ) → Hyp A (Γ ∙ B)

Mon : (P : Cxt → Set) → Set
Mon P = ∀{Γ Δ} (τ : Γ ≤ Δ) → P Δ → P Γ

monH : ∀{A} → Mon (Hyp A)
monH ε      ()
monH (weak τ) x       = pop (monH τ x)
monH (lift τ) top     = top
monH (lift τ) (pop x) = pop (monH τ x)

monH-id : ∀{Γ A} (x : Hyp A Γ) → monH id≤ x ≡ x
monH-id top     = refl
monH-id (pop x) = cong pop (monH-id x)

monH• : ∀{Γ Δ Φ A} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) (x : Hyp A Φ) → monH (τ • σ) x ≡ monH τ (monH σ x)
monH• ε ε ()
monH• (weak τ) σ        x       = cong pop (monH• τ σ x)
monH• (lift τ) (weak σ) x       = cong pop (monH• τ σ x)
monH• (lift τ) (lift σ) top     = refl
monH• (lift τ) (lift σ) (pop x) = cong pop (monH• τ σ x)

{-# REWRITE monH-id monH• #-}

□ : (P : Cxt → Set) → Cxt → Set
□ P Γ = ∀{Δ} (τ : Δ ≤ Γ) → P Δ

mon□ : ∀{P} → Mon (□ P)
mon□ τ x τ′ = x (τ′ • τ)

infix 1 _→̇_
infixr 2 _⇒̂_

-- Presheaf morphism

_→̇_ : (P Q : Cxt → Set) → Set
P →̇ Q = ∀{Γ} → P Γ → Q Γ

⟨_⊙_⟩→̇_ : (P Q R : Cxt → Set) → Set
⟨ P ⊙ Q ⟩→̇ R = ∀{Γ} → P Γ → Q Γ → R Γ

⟨_⊙_⊙_⟩→̇_ : (P Q R S : Cxt → Set) → Set
⟨ P ⊙ Q ⊙ R ⟩→̇ S = ∀{Γ} → P Γ → Q Γ → R Γ → S Γ

-- Pointwise presheaf arrow (not a presheaf)

CFun : (P Q : Cxt → Set) → Cxt → Set
CFun P Q Γ = P Γ → Q Γ

-- Presheaf exponentional (Kripke function space)

KFun : (P Q : Cxt → Set) → Cxt → Set
KFun P Q = □ (CFun P Q)

-- Again, in expanded form.

_⇒̂_  : (P Q : Cxt → Set) → Cxt → Set
P ⇒̂ Q = λ Γ → ∀{Δ} (τ : Δ ≤ Γ) → P Δ → Q Δ

-- -}
-- -}
-- -}
-- -}
-- -}
