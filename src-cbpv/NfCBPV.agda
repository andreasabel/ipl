{-# OPTIONS --rewriting #-}

open import Library hiding (_×̇_)

postulate Base : Set

mutual

  -- Value types

  data VTy : Set where
    base    : (o : Base) → VTy
    0̇ 1̇     : VTy
    _+̇_ _×̇_ : (P₁ P₂ : VTy) → VTy
    thunk   : (N : CTy) → VTy      -- U

  -- Computation types

  data CTy : Set where
    comp   : (P : VTy) → CTy     -- F
    _⊤̇_    : CTy
    _&_    : (N₁ N₂ : CTy) → CTy
    _⇒_    : (P : VTy) (N : CTy) → CTy

-- Environments only contain values

Cxt = List VTy

-- variable Γ Δ Φ : Cxt

pattern zero = here refl
pattern suc  = there

-- Normal forms

mutual

  data Val : (P : VTy) (Γ : Cxt) → Set where
    var   : ∀{Γ P}     (x : P ∈ Γ)                     → Val P Γ
    unit  : ∀{Γ}                                       → Val 1̇ Γ
    pair  : ∀{Γ P₁ P₂} (v₁ : Val P₁ Γ) (v₂ : Val P₂ Γ) → Val (P₁ ×̇ P₂) Γ
    inl   : ∀{Γ P₁ P₂} (v : Val P₁ Γ)                  → Val (P₁ +̇ P₂) Γ
    inr   : ∀{Γ P₁ P₂} (v : Val P₂ Γ)                  → Val (P₁ +̇ P₂) Γ
    thunk : ∀{Γ N}     (t : Comp N Γ)                  → Val (thunk N) Γ

  data Comp : (N : CTy) (Γ : Cxt) → Set where
    ret   : ∀{Γ P} → Comp (comp P) Γ
    rcrd₀ : ∀{Γ} → Comp {!⊤̇!} Γ
    rcrd₂ : ∀{Γ N₁ N₂} → (t₁ : Comp N₁ Γ) (t₂ : Comp N₂ Γ) → Comp (N₁ & N₂) Γ
    abs   : ∀{Γ P N} → (t : Comp N (P ∷ Γ)) → Comp (P ⇒ N) Γ
