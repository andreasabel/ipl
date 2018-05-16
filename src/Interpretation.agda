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

Fun : (Γ : Cxt) (A : Form) → Set
Fun Γ A = (γ : C⦅ Γ ⦆) → T⦅ A ⦆

Mor : (Γ Δ : Cxt) → Set
Mor Γ Δ = (γ : C⦅ Γ ⦆) → C⦅ Δ ⦆

H⦅_⦆ : ∀{Γ A} (x : Hyp Γ A) → Fun Γ A
H⦅ top   ⦆ = proj₂
H⦅ pop x ⦆ = H⦅ x ⦆ ∘ proj₁

D⦅_⦆ : ∀{Γ A} (t : Γ ⊢ A) → Fun Γ A
D⦅ hyp x ⦆      = H⦅ x ⦆
D⦅ impI t ⦆     = curry D⦅ t ⦆
D⦅ impE t u ⦆ γ = D⦅ t ⦆ γ (D⦅ u ⦆ γ)
D⦅ andI t u ⦆   = < D⦅ t ⦆ , D⦅ u ⦆ >
D⦅ andE₁ t ⦆    = proj₁ ∘ D⦅ t ⦆
D⦅ andE₂ t ⦆    = proj₂ ∘ D⦅ t ⦆
D⦅ orI₁ t ⦆     = inj₁ ∘ D⦅ t ⦆
D⦅ orI₂ t ⦆     = inj₂ ∘ D⦅ t ⦆
D⦅ orE t u v ⦆ γ = [ D⦅ u ⦆ ∘ (γ ,_) , D⦅ v ⦆ ∘ (γ ,_) ] (D⦅ t ⦆ γ)
D⦅ falseE t ⦆  = ⊥-elim ∘ D⦅ t ⦆
D⦅ trueI ⦆      = _

consistency : (t : ε ⊢ False) → ⊥
consistency t = D⦅ t ⦆ _

R⦅_⦆ : ∀{Γ Δ} (τ : Γ ≤ Δ) (γ : C⦅ Γ ⦆) → C⦅ Δ ⦆
R⦅_⦆ {Γ} {ε}     τ γ = _
R⦅_⦆ {Γ} {Δ ∙ A} τ γ = R⦅ τ ∘ pop ⦆ γ , H⦅ τ top ⦆ γ
