{-# OPTIONS --rewriting #-}

module NfCBPVLaws where

open import Library hiding (_×̇_)

open import NfCBPV

-- NB: mon⁺ is a comonad coalgebra

module MonIsComonadCoalgebra where

  mon-id : ∀ (P : Ty⁺) {Γ} (a : ⟦ P ⟧⁺ Γ) → mon⁺ P a ⊆-refl ≡ a
  mon-id (base o)  x         = {!monVar-id!}
  mon-id (P₁ ×̇ P₂) (a₁ , a₂) = cong₂ _,_ (mon-id P₁ a₁) (mon-id P₂ a₂)
  mon-id (Σ̇ I Ps)  (i  ,  a) = cong (i ,_) (mon-id (Ps i) a)
  mon-id (□̇ N)     f         = funExtH (funExt (λ τ → cong f {!!})) -- ⊆-trans ⊆-refl τ ≡ τ

  -- Identity: extract ∘ mon⁺ ≡ id

  extract∘mon : ∀ (P : Ty⁺) {Γ} → extract ∘ mon⁺ P ≗ id {A = ⟦ P ⟧⁺ Γ}
  extract∘mon = mon-id

  -- Associativity: □-map (mon⁺ P) ∘ mon⁺ P ≡ duplicate ∘ mon⁺ P

  mon∘mon : ∀ (P : Ty⁺) {Γ} (a : ⟦ P ⟧⁺ Γ) {Δ} {τ : Γ ⊆ Δ} {Φ} {τ' : Δ ⊆ Φ} →
    mon⁺ P (mon⁺ P a τ) τ' ≡ mon⁺ P a (⊆-trans τ τ')
  mon∘mon (base o)  x         = {!!}  -- monVar∘monVar
  mon∘mon (P₁ ×̇ P₂) (a₁ , a₂) = cong₂ _,_ (mon∘mon P₁ a₁) (mon∘mon P₂ a₂)
  mon∘mon (Σ̇ I Ps)  (i  , a)  = cong (i ,_) (mon∘mon (Ps i) a)
  mon∘mon (□̇ N)     f         = {!!}  -- □-mon∘□-mon

  map-mon∘mon : ∀ (P : Ty⁺) {Γ} → □-map (mon⁺ P) ∘ mon⁺ P ≗ duplicate ∘ mon⁺ P {Γ}
  map-mon∘mon P a = funExtH $ funExt λ τ → funExtH $ funExt λ τ' → mon∘mon P a


module RunIsMonadAlgebra where

  -- Identity: run⁻ N ∘ return ≡ id

  -- Associativity: run⁻ N ∘ ◇-map (run⁻ N) ≡ run⁻ N ∘ join


-- ◇ preserves monotonicity
------------------------------------------------------------------------

-- This needs weakening of neutrals

◇-mon : Mon A → Mon (◇ A)
◇-mon mA (return a) τ = return (mA a τ)
◇-mon mA (bind u c) τ = bind {!!} (◇-mon mA c (refl ∷ τ)) -- need monotonicity of Ne
◇-mon mA (case x t) τ = case (monVar x τ) (λ i → ◇-mon mA (t i) (refl ∷ τ))
◇-mon mA (split x c) τ = split (monVar x τ) (◇-mon mA c (refl ∷ refl ∷ τ))

-- From ◇-mon we get □-run

□-run : Run B → Run (□ B)
□-run rB c = rB ∘ ◇-map extract ∘ ◇-mon □-mon c


freshᶜ₀ : (Γ : Cxt) → ◇ ⟦ Γ ⟧ᶜ Γ
freshᶜ₀ [] = return []
freshᶜ₀ (P ∷ Γ) = ◇-ext $
  □-weak (◇-mon (monᶜ Γ) (freshᶜ₀ Γ)) -- BAD, use of ◇-mon
  ⋉ fresh◇
-- freshᶜ (P ∷ Γ) = ◇-ext $
--   (λ τ → ◇-mon (monᶜ Γ) (freshᶜ Γ) (⊆-trans (_ ∷ʳ ⊆-refl) τ))  -- BAD, use of ◇-mon
--   ⋉ fresh◇


freshG₀ : □ (◇ ⟦ Γ ⟧ᶜ) Γ
-- freshG₀ : (τ : Γ ⊆ Δ) → ◇ ⟦ Γ ⟧ᶜ Δ
freshG₀ [] = return []
freshG₀ (P   ∷ʳ τ) = ◇-mon (monᶜ _) (freshG₀ τ) (P ∷ʳ ⊆-refl)  -- BAD, use of ◇-mon
freshG₀ (refl ∷ τ) = ◇-ext $ (λ τ₁ → freshG₀ (⊆-trans τ (⊆-trans (_ ∷ʳ ⊆-refl) τ₁))) ⋉ fresh◇
