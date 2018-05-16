{-# OPTIONS --rewriting #-}

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

infix 3 _≤_

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤ : ∀{Γ} → Γ ≤ Γ
  weak : ∀{Γ Δ A} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  lift : ∀{Γ Δ A} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

postulate lift-id≤ : ∀{Γ A} → lift id≤ ≡ id≤ {Γ ∙ A}
{-# REWRITE lift-id≤ #-}

monH : ∀{Γ Δ A} (τ : Γ ≤ Δ) (x : Hyp Δ A) → Hyp Γ A
monH id≤      x       = x
monH (weak τ) x       = pop (monH τ x)
monH (lift τ) top     = top
monH (lift τ) (pop x) = pop (monH τ x)

_•_ : ∀{Γ Δ Φ} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) → Γ ≤ Φ
id≤ • σ = σ
weak τ • σ = weak (τ • σ)
lift τ • id≤ = lift τ
lift τ • weak σ = weak (τ • σ)
lift τ • lift σ = lift (τ • σ)

monH• : ∀{Γ Δ Φ A} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) (x : Hyp Φ A) → monH (τ • σ) x ≡ monH τ (monH σ x)
monH• id≤      σ        x       = refl
monH• (weak τ) σ        x       = cong pop (monH• τ σ x)
monH• (lift τ) id≤      x       = refl
monH• (lift τ) (weak σ) x       = cong pop (monH• τ σ x)
monH• (lift τ) (lift σ) top     = refl
monH• (lift τ) (lift σ) (pop x) = cong pop (monH• τ σ x)

{-# REWRITE monH• #-}
