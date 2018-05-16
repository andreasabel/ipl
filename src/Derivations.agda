-- Syntax

open import Library

module Derivations (Base : Set) where

import Formulas; open module Form = Formulas Base

-- Derivations

infix 2 _⊢_

data _⊢_ (Γ : Cxt) : (A : Form) → Set where
  hyp    : ∀{A} (x : Hyp Γ A) → Γ ⊢ A
  impI   : ∀{A B} (t : Γ ∙ A ⊢ B) → Γ ⊢ A ⇒ B
  impE   : ∀{A B} (t : Γ ⊢ A ⇒ B) (u : Γ ⊢ A) → Γ ⊢ B
  andI   : ∀{A B} (t : Γ ⊢ A) (u : Γ ⊢ B) → Γ ⊢ A ∧ B
  andE₁  : ∀{A B} (t : Γ ⊢ A ∧ B) → Γ ⊢ A
  andE₂  : ∀{A B} (t : Γ ⊢ A ∧ B) → Γ ⊢ B
  orI₁   : ∀{A B} (t : Γ ⊢ A) → Γ ⊢ A ∨ B
  orI₂   : ∀{A B} (t : Γ ⊢ B) → Γ ⊢ A ∨ B
  orE    : ∀{A B C} (t : Γ ⊢ A ∨ B) (u : Γ ∙ A ⊢ C) (v : Γ ∙ B ⊢ C) → Γ ⊢ C
  falseE : ∀{A} (t : Γ ⊢ False) → Γ ⊢ A
  trueI  : Γ ⊢ True

-- Example derivation

andComm : ∀{A B} → ε ⊢ A ∧ B ⇒ B ∧ A
andComm = impI (andI (andE₂ (hyp top)) (andE₁ (hyp top)))

-- Weakening

monD : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Γ ⊢ A) → Δ ⊢ A
monD τ (hyp x)     = hyp (τ x)
monD τ (impI t)    = impI (monD (lift τ) t)
monD τ (impE t u)  = impE (monD τ t) (monD τ u)
monD τ (andI t u)  = andI (monD τ t) (monD τ u)
monD τ (andE₁ t)   = andE₁ (monD τ t)
monD τ (andE₂ t)   = andE₂ (monD τ t)
monD τ (orI₁ t)    = orI₁ (monD τ t)
monD τ (orI₂ t)    = orI₂ (monD τ t)
monD τ (orE t u v) = orE (monD τ t) (monD (lift τ) u) (monD (lift τ) v)
monD τ (falseE t)  = falseE (monD τ t)
monD τ trueI       = trueI
