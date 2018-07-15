{-# OPTIONS --rewriting #-}

-- Set-theoretic interpretation and consistency

open import Library

module Interpretation (Base : Set) (B⦅_⦆ : Base → Set) where

import Formulas   ; open module Form = Formulas    Base
import Derivations; open module Der  = Derivations Base

T⦅_⦆ : (A : Form) → Set
T⦅ Atom P ⦆ = B⦅ P ⦆
T⦅ True ⦆ = ⊤
T⦅ False ⦆ = ⊥
T⦅ A ∨ B ⦆ = T⦅ A ⦆ ⊎ T⦅ B ⦆
T⦅ A ∧ B ⦆ = T⦅ A ⦆ × T⦅ B ⦆
T⦅ A ⇒ B ⦆ = T⦅ A ⦆ → T⦅ B ⦆

C⦅_⦆ : (Γ : Cxt) → Set
C⦅ ε ⦆ = ⊤
C⦅ Γ ∙ A ⦆ = C⦅ Γ ⦆ × T⦅ A ⦆

Fun' : (Γ : Cxt) (S : Set) → Set
Fun' Γ S = (γ : C⦅ Γ ⦆) → S

Fun : (Γ : Cxt) (A : Form) → Set
Fun Γ A = Fun' Γ T⦅ A ⦆

Mor : (Γ Δ : Cxt) → Set
Mor Γ Δ = Fun' Γ C⦅ Δ ⦆

H⦅_⦆ : ∀{Γ A} (x : Hyp A Γ) → Fun Γ A
H⦅ top   ⦆ = proj₂
H⦅ pop x ⦆ = H⦅ x ⦆ ∘ proj₁

D⦅_⦆ : ∀{Γ A} (t : Γ ⊢ A) → Fun Γ A
D⦅ hyp x ⦆      = H⦅ x ⦆
D⦅ impI t ⦆     = curry D⦅ t ⦆
D⦅ impE t u ⦆   = apply D⦅ t ⦆ D⦅ u ⦆
D⦅ andI t u ⦆   = < D⦅ t ⦆ , D⦅ u ⦆ >
D⦅ andE₁ t ⦆    = proj₁ ∘ D⦅ t ⦆
D⦅ andE₂ t ⦆    = proj₂ ∘ D⦅ t ⦆
D⦅ orI₁ t ⦆     = inj₁ ∘ D⦅ t ⦆
D⦅ orI₂ t ⦆     = inj₂ ∘ D⦅ t ⦆
D⦅ orE t u v ⦆ = caseof D⦅ t ⦆ D⦅ u ⦆ D⦅ v ⦆
D⦅ falseE t ⦆  = ⊥-elim ∘ D⦅ t ⦆
D⦅ trueI ⦆      = _

consistency : (t : ε ⊢ False) → ⊥
consistency t = D⦅ t ⦆ _

Ne⦅_⦆ : ∀{Γ A} (t : Ne Γ A) → Fun Γ A
Ne⦅_⦆ = D⦅_⦆ ∘ ne[_]

Nf⦅_⦆ : ∀{Γ A} (t : Nf Γ A) → Fun Γ A
Nf⦅_⦆ = D⦅_⦆ ∘ nf[_]

-- Functor

R⦅_⦆ : ∀{Γ Δ} (τ : Γ ≤ Δ) → Mor Γ Δ
R⦅ id≤    ⦆ = id
R⦅ weak τ ⦆ = R⦅ τ ⦆ ∘ proj₁
R⦅ lift τ ⦆ = R⦅ τ ⦆ ×̇ id

-- Kripke application

kapp : ∀ A B {Γ} (f : Fun Γ (A ⇒ B)) {Δ} (τ : Δ ≤ Γ) (a : Fun Δ A) → Fun Δ B
kapp A B f τ a δ = f (R⦅ τ ⦆ δ) (a δ)

-- Naturality

natH  : ∀{Γ Δ A} (τ : Δ ≤ Γ) (x : Hyp A Γ) → H⦅ monH τ x ⦆ ≡ H⦅ x ⦆ ∘ R⦅ τ ⦆
natH id≤ x = refl
natH (weak τ) x = cong (_∘ proj₁) (natH τ x)
natH (lift τ) top = refl
natH (lift τ) (pop x) = cong (_∘ proj₁) (natH τ x)

{-# REWRITE natH #-}

natR : ∀{Γ Δ Φ} (σ : Φ ≤ Δ) (τ : Δ ≤ Γ) → R⦅ σ • τ ⦆ ≡ R⦅ τ ⦆ ∘ R⦅ σ ⦆
natR id≤ τ = refl
natR (weak σ) τ = cong (_∘ proj₁) (natR σ τ)
natR (lift σ) id≤ = refl
natR (lift σ) (weak τ) = cong (_∘ proj₁) (natR σ τ)
natR (lift σ) (lift τ) = cong (_×̇ id) (natR σ τ)

{-# REWRITE natR #-}

natD : ∀{Γ Δ A} (τ : Δ ≤ Γ) (t : Γ ⊢ A) → D⦅ monD τ t ⦆ ≡ D⦅ t ⦆ ∘ R⦅ τ ⦆
natD τ (hyp x) = natH τ x
natD τ (impI t) = cong curry (natD (lift τ) t)
natD τ (impE t u) = cong₂ apply (natD τ t) (natD τ u)
natD τ (andI t u) = cong₂ <_,_> (natD τ t) (natD τ u)
natD τ (andE₁ t) = cong (proj₁ ∘_) (natD τ t)
natD τ (andE₂ t) = cong (proj₂ ∘_) (natD τ t)
natD τ (orI₁ t) = cong (inj₁ ∘_) (natD τ t)
natD τ (orI₂ t) = cong (inj₂ ∘_) (natD τ t)
natD τ (orE t u v) = cong₃ caseof (natD τ t) (natD (lift τ) u) (natD (lift τ) v)
natD τ (falseE t) = cong (⊥-elim ∘_) (natD τ t)
natD τ trueI = funExt λ _ → refl

{-# REWRITE natD #-}

-- -}
