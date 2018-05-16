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

-- For normal forms, we use the standard presentation.
-- Normal forms are not unique.

-- Normality as predicate

mutual
  data Neutral {Γ} {A} : (t : Γ ⊢ A) → Set where
    hyp : (x : Hyp Γ A) → Neutral (hyp x)
    impE : ∀{B} {t : Γ ⊢ B ⇒ A} {u : Γ ⊢ B} (ne : Neutral t) (nf : Normal u) → Neutral (impE t u)
    andE₁ : ∀{B} {t : Γ ⊢ A ∧ B} (ne : Neutral t) → Neutral (andE₁ t)
    andE₂ : ∀{B} {t : Γ ⊢ B ∧ A} (ne : Neutral t) → Neutral (andE₂ t)

  data Normal {Γ} : ∀{A} (t : Γ ⊢ A) → Set where
    ne     : ∀{A} {t : Γ ⊢ A} (ne : Neutral t) → Normal t
    impI   : ∀{A B} (t : Γ ∙ A ⊢ B) (nf : Normal t) → Normal (impI t)
    andI   : ∀{A B} (t : Γ ⊢ A) (u : Γ ⊢ B) (nf₁ : Normal t) (nf₂ : Normal u) → Normal (andI t u)
    orI₁   : ∀{A B} {t : Γ ⊢ A} (nf : Normal t) → Normal (orI₁ {Γ} {A} {B} t)
    orI₂   : ∀{A B} {t : Γ ⊢ B} (nf : Normal t) → Normal (orI₂ {Γ} {A} {B} t)
    orE    : ∀{A B C} {t : Γ ⊢ A ∨ B} {u : Γ ∙ A ⊢ C} {v : Γ ∙ B ⊢ C}
             (ne : Neutral t) (nf₁ : Normal u) (nf₂ : Normal v) → Normal (orE t u v)
    falseE : ∀{A} {t : Γ ⊢ False} (ne : Neutral t) → Normal (falseE {Γ} {A} t)
    trueI  : Normal trueI

-- Intrinsic normality

mutual
  data Ne (Γ : Cxt) (A : Form) : Set where
    hyp    : ∀    (x : Hyp Γ A) → Ne Γ A
    impE   : ∀{B} (t : Ne Γ (B ⇒ A)) (u : Nf Γ B) → Ne Γ A
    andE₁  : ∀{B} (t : Ne Γ (A ∧ B)) → Ne Γ A
    andE₂  : ∀{B} (t : Ne Γ (B ∧ A)) → Ne Γ A

  data Nf (Γ : Cxt) : (A : Form) → Set where
    ne     : ∀{A} (t : Ne Γ A) → Nf Γ A
    impI   : ∀{A B} (t : Nf (Γ ∙ A) B) → Nf Γ (A ⇒ B)
    andI   : ∀{A B} (t : Nf Γ A) (u : Nf Γ B) → Nf Γ (A ∧ B)
    orI₁   : ∀{A B} (t : Nf Γ A) → Nf Γ (A ∨ B)
    orI₂   : ∀{A B} (t : Nf Γ B) → Nf Γ (A ∨ B)
    orE    : ∀{A B C} (t : Ne Γ (A ∨ B)) (u : Nf (Γ ∙ A) C) (v : Nf (Γ ∙ B) C) → Nf Γ C
    falseE : ∀{A} (t : Ne Γ False) → Nf Γ A
    trueI  : Nf Γ True

mutual

  monNe : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Ne Γ A) → Ne Δ A
  monNe τ (hyp x)     = hyp (τ x)
  monNe τ (impE t u)  = impE (monNe τ t) (monNf τ u)
  monNe τ (andE₁ t)   = andE₁ (monNe τ t)
  monNe τ (andE₂ t)   = andE₂ (monNe τ t)

  monNf : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Nf Γ A) → Nf Δ A
  monNf τ (ne t)     = ne (monNe τ t)
  monNf τ (impI t)    = impI (monNf (lift τ) t)
  monNf τ (andI t u)  = andI (monNf τ t) (monNf τ u)
  monNf τ (orI₁ t)    = orI₁ (monNf τ t)
  monNf τ (orI₂ t)    = orI₂ (monNf τ t)
  monNf τ (orE t u v) = orE (monNe τ t) (monNf (lift τ) u) (monNf (lift τ) v)
  monNf τ (falseE t)  = falseE (monNe τ t)
  monNf τ trueI       = trueI
