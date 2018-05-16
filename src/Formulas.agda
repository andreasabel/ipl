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

-- Hypotheses

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form) → Cxt

infixl 4 _∙_

data Hyp : (Γ : Cxt) (A : Form) → Set where
  top : ∀{Γ A} → Hyp (Γ ∙ A) A
  pop : ∀{Γ A B} (x : Hyp Γ A) → Hyp (Γ ∙ B) A

-- Context extension and permutation

_≤_ : (Γ Δ : Cxt) → Set
Γ ≤ Δ = ∀{A} → Hyp Δ A → Hyp Γ A

infix 3 _≤_

lift : ∀{Γ Δ A} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A
lift τ top = top
lift τ (pop x) = pop (τ x)
