{-# OPTIONS --rewriting #-}

-- Syntax

open import Library

module Derivations (Base : Set) where

import Formulas; private open module Form = Formulas Base
-- open import Formulas Base public

-- Derivations

infix 2 _⊢_

data _⊢_ (Γ : Cxt) : (A : Form) → Set where
  hyp    : ∀{A} (x : Hyp A Γ) → Γ ⊢ A
  impI   : ∀{A B} (t : Γ ∙ A ⊢ B) → Γ ⊢ A ⇒ B
  impE   : ∀{A B} (t : Γ ⊢ A ⇒ B) (u : Γ ⊢ A) → Γ ⊢ B
  andI   : ∀{A B} (t : Γ ⊢ A) (u : Γ ⊢ B) → Γ ⊢ A ∧ B
  andE₁  : ∀{A B} (t : Γ ⊢ A ∧ B) → Γ ⊢ A
  andE₂  : ∀{A B} (t : Γ ⊢ A ∧ B) → Γ ⊢ B
  orI₁   : ∀{A B} (t : Γ ⊢ A) → Γ ⊢ A ∨ B
  orI₂   : ∀{A B} (t : Γ ⊢ B) → Γ ⊢ A ∨ B
  orE    : ∀{A B C} (t : Γ ⊢ A ∨ B) (u : Γ ∙ A ⊢ C) (v : Γ ∙ B ⊢ C) → Γ ⊢ C
  falseE : ∀{C} (t : Γ ⊢ False) → Γ ⊢ C
  trueI  : Γ ⊢ True

-- Example derivation

andComm : ∀{A B} → ε ⊢ A ∧ B ⇒ B ∧ A
andComm = impI (andI (andE₂ (hyp top)) (andE₁ (hyp top)))

-- Weakening

Tm = λ A Γ → Γ ⊢ A

monD : ∀{A} → Mon (Tm A)
monD τ (hyp x)     = hyp (monH τ x)
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

monD-id : ∀{Γ A} (t : Γ ⊢ A) → monD id≤ t ≡ t
monD-id (hyp x) = refl
monD-id (impI t) = cong impI (monD-id t)  -- REWRITE lift-id≤
monD-id (impE t u) = cong₂ impE (monD-id t) (monD-id u)
monD-id (andI t u) = cong₂ andI (monD-id t) (monD-id u)
monD-id (andE₁ t) = cong andE₁ (monD-id t)
monD-id (andE₂ t) = cong andE₂ (monD-id t)
monD-id (orI₁ t) = cong orI₁ (monD-id t)
monD-id (orI₂ t) = cong orI₂ (monD-id t)
monD-id (orE t u v) = cong₃ orE (monD-id t) (monD-id u) (monD-id v)
monD-id (falseE t) = cong falseE (monD-id t)
monD-id trueI = refl

-- For normal forms, we use the standard presentation.
-- Normal forms are not unique.

-- Normality as predicate

mutual
  data Neutral {Γ} {A} : (t : Γ ⊢ A) → Set where
    hyp : (x : Hyp A Γ) → Neutral (hyp x)
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
    hyp    : ∀    (x : Hyp A Γ) → Ne Γ A
    impE   : ∀{B} (t : Ne Γ (B ⇒ A)) (u : Nf Γ B) → Ne Γ A
    andE₁  : ∀{B} (t : Ne Γ (A ∧ B)) → Ne Γ A
    andE₂  : ∀{B} (t : Ne Γ (B ∧ A)) → Ne Γ A

  data Nf (Γ : Cxt) : (A : Form) → Set where
    -- ne     : ∀{A} (t : Ne Γ A) → Nf Γ A   -- allows η-short nfs
    ne     : ∀{P} (t : Ne Γ (Atom P)) → Nf Γ (Atom P)
    impI   : ∀{A B} (t : Nf (Γ ∙ A) B) → Nf Γ (A ⇒ B)
    andI   : ∀{A B} (t : Nf Γ A) (u : Nf Γ B) → Nf Γ (A ∧ B)
    orI₁   : ∀{A B} (t : Nf Γ A) → Nf Γ (A ∨ B)
    orI₂   : ∀{A B} (t : Nf Γ B) → Nf Γ (A ∨ B)
    orE    : ∀{A B C} (t : Ne Γ (A ∨ B)) (u : Nf (Γ ∙ A) C) (v : Nf (Γ ∙ B) C) → Nf Γ C
    falseE : ∀{A} (t : Ne Γ False) → Nf Γ A
    trueI  : Nf Γ True

-- Presheaf-friendly argument order

Ne' = λ A Γ → Ne Γ A
Nf' = λ A Γ → Nf Γ A

-- Admissible false-Elimination from a normal proof of false (using case splits)

falseE! : ∀{A} → Nf' False →̇ Nf' A
-- falseE! (ne t)       = falseE t  -- only for η-short
falseE! (orE t t₁ t₂) = orE t (falseE! t₁) (falseE! t₂)
falseE! (falseE t)   = falseE t

-- Ne' and Nf' are presheaves over (Cxt, ≤)

mutual

  monNe : ∀{A} → Mon (Ne' A)
  monNe τ (hyp x)     = hyp (monH τ x)
  monNe τ (impE t u)  = impE (monNe τ t) (monNf τ u)
  monNe τ (andE₁ t)   = andE₁ (monNe τ t)
  monNe τ (andE₂ t)   = andE₂ (monNe τ t)

  monNf : ∀{A} → Mon (Nf' A)
  monNf τ (ne t)     = ne (monNe τ t)
  monNf τ (impI t)    = impI (monNf (lift τ) t)
  monNf τ (andI t u)  = andI (monNf τ t) (monNf τ u)
  monNf τ (orI₁ t)    = orI₁ (monNf τ t)
  monNf τ (orI₂ t)    = orI₂ (monNf τ t)
  monNf τ (orE t u v) = orE (monNe τ t) (monNf (lift τ) u) (monNf (lift τ) v)
  monNf τ (falseE t)  = falseE (monNe τ t)
  monNf τ trueI       = trueI

-- Forgetting normality

mutual
  ne[_] : ∀{Γ A} (t : Ne Γ A) → Γ ⊢ A
  ne[ hyp x ]     = hyp x
  ne[ impE t u ]  = impE ne[ t ] nf[ u ]
  ne[ andE₁ t ]   = andE₁ ne[ t ]
  ne[ andE₂ t ]   = andE₂ ne[ t ]

  nf[_] : ∀{Γ A} (t : Nf Γ A) → Γ ⊢ A
  nf[ ne t ]      = ne[ t ]
  nf[ impI t ]    = impI nf[ t ]
  nf[ andI t u ]  = andI nf[ t ] nf[ u ]
  nf[ orI₁ t ]    = orI₁ nf[ t ]
  nf[ orI₂ t ]    = orI₂ nf[ t ]
  nf[ orE t u v ] = orE ne[ t ] nf[ u ] nf[ v ]
  nf[ falseE t ]  = falseE ne[ t ]
  nf[ trueI ]     = trueI

mutual

  monD-ne : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Ne Γ A) → ne[ monNe τ t ] ≡ monD τ ne[ t ]
  monD-ne τ (hyp x)     = refl
  monD-ne τ (impE t u)  = cong₂ impE (monD-ne τ t) (monD-nf τ u)
  monD-ne τ (andE₁ t)   = cong andE₁ (monD-ne τ t)
  monD-ne τ (andE₂ t)   = cong andE₂ (monD-ne τ t)

  monD-nf : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Nf Γ A) → nf[ monNf τ t ] ≡ monD τ nf[ t ]
  monD-nf τ (ne t)      = monD-ne τ t
  monD-nf τ (impI t)    = cong impI (monD-nf (lift τ) t)
  monD-nf τ (andI t u)  = cong₂ andI (monD-nf τ t) (monD-nf τ u)
  monD-nf τ (orI₁ t)    = cong orI₁ (monD-nf τ t)
  monD-nf τ (orI₂ t)    = cong orI₂ (monD-nf τ t)
  monD-nf τ (orE t u v) = cong₃ orE (monD-ne τ t) (monD-nf (lift τ) u) (monD-nf (lift τ) v)
  monD-nf τ (falseE t)  = cong falseE (monD-ne τ t)
  monD-nf τ trueI       = refl

  -- monD-ne : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Ne Γ A) → monD τ ne[ t ] ≡ ne[ monNe τ t ]
  -- monD-ne τ (hyp x)     = refl
  -- monD-ne τ (impE t u)  = cong₂ impE (monD-ne τ t) (monD-nf τ u)
  -- monD-ne τ (andE₁ t)   = cong andE₁ (monD-ne τ t)
  -- monD-ne τ (andE₂ t)   = cong andE₂ (monD-ne τ t)

  -- monD-nf : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Nf Γ A) → monD τ nf[ t ] ≡ nf[ monNf τ t ]
  -- monD-nf τ (ne t)      = monD-ne τ t
  -- monD-nf τ (impI t)    = cong impI (monD-nf (lift τ) t)
  -- monD-nf τ (andI t u)  = cong₂ andI (monD-nf τ t) (monD-nf τ u)
  -- monD-nf τ (orI₁ t)    = cong orI₁ (monD-nf τ t)
  -- monD-nf τ (orI₂ t)    = cong orI₂ (monD-nf τ t)
  -- monD-nf τ (orE t u v) = cong₃ orE (monD-ne τ t) (monD-nf (lift τ) u) (monD-nf (lift τ) v)
  -- monD-nf τ (falseE t)  = cong falseE (monD-ne τ t)
  -- monD-nf τ trueI       = refl

{-# REWRITE monD-ne monD-nf #-}
