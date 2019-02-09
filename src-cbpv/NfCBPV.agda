{-# OPTIONS --rewriting #-}

open import Library hiding (_×̇_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

postulate Base : Set

set = ℕ
El  = Fin

mutual

  -- Value types

  data VTy : Set where
    base    : (o : Base) → VTy
    _×̇_     : (P₁ P₂ : VTy) → VTy
    Σ̇       : (I : set) (P : El I → VTy) → VTy
    thunk   : (N : CTy) → VTy      -- U

  -- Computation types

  data CTy : Set where
    comp   : (P : VTy) → CTy     -- F
    Π      : (I : set) (P : El I → CTy) → CTy
    _⇒_    : (P : VTy) (N : CTy) → CTy

-- Environments only contain values

Cxt = List VTy

-- variable Γ Δ Φ : Cxt

pattern here! = here refl
-- pattern suc  = there

-- Terms

module _ (Comp : CTy → Cxt → Set) where

  data Val' : (P : VTy) (Γ : Cxt) → Set where
    var   : ∀{Γ P}     (x : P ∈ Γ)                       → Val' P Γ
    pair  : ∀{Γ P₁ P₂} (v₁ : Val' P₁ Γ) (v₂ : Val' P₂ Γ) → Val' (P₁ ×̇ P₂) Γ
    inj   : ∀{Γ I P} i (v : Val' (P i) Γ)                → Val' (Σ̇ I P) Γ
    thunk : ∀{Γ N}     (t : Comp N Γ)                    → Val' (thunk N) Γ

mutual

  data Val : (P : VTy) (Γ : Cxt) → Set where
    var   : ∀{Γ P}     (x : P ∈ Γ)                     → Val P Γ
    pair  : ∀{Γ P₁ P₂} (v₁ : Val P₁ Γ) (v₂ : Val P₂ Γ) → Val (P₁ ×̇ P₂) Γ
    inj   : ∀{Γ I P} i (v : Val (P i) Γ)               → Val (Σ̇ I P) Γ
    thunk : ∀{Γ N}     (t : Comp N Γ)                  → Val (thunk N) Γ

  data Comp : (N : CTy) (Γ : Cxt) → Set where
    -- introductions
    ret   : ∀{Γ P}       (v : Val P Γ)                → Comp (comp P) Γ
    rec   : ∀{Γ I N}     (t : ∀ i → Comp (N i) Γ)     → Comp (Π I N) Γ
    abs   : ∀{Γ P N}     (t : Comp N (P ∷ Γ))         → Comp (P ⇒ N) Γ
    -- positive eliminations
    split : ∀{Γ P₁ P₂ N} (v : Val (P₁ ×̇ P₂) Γ) (t : Comp N (P₂ ∷ P₁ ∷ Γ)) → Comp N Γ
    case  : ∀{Γ I P N}   (v : Val (Σ̇ I P) Γ) (t : ∀ i → Comp N (P i ∷ Γ)) → Comp N Γ
    force : ∀{Γ N}       (v : Val (thunk N) Γ)   → Comp N Γ
    -- binds
    letv  : ∀{Γ P N}     (v : Val P Γ)         (t : Comp N (P ∷ Γ)) → Comp N Γ
    bind  : ∀{Γ P N}     (u : Comp (comp P) Γ) (t : Comp N (P ∷ Γ)) → Comp N Γ
    -- negative elimination
    prj   : ∀{Γ I N} i   (t : Comp (Π I N) Γ)                        → Comp (N i) Γ
    app   : ∀{Γ P N}     (t : Comp (P ⇒ N) Γ)   (v : Val P Γ)        → Comp N Γ

-- Normal forms

mutual

  data NVal : (P : VTy) (Γ : Cxt) → Set where
    var   : ∀{Γ P}     (x : P ∈ Γ)                     → NVal P Γ
    pair  : ∀{Γ P₁ P₂} (v₁ : NVal P₁ Γ) (v₂ : NVal P₂ Γ) → NVal (P₁ ×̇ P₂) Γ
    inj   : ∀{Γ I P} i (v : NVal (P i) Γ)               → NVal (Σ̇ I P) Γ
    thunk : ∀{Γ N}     (t : NComp N Γ)                  → NVal (thunk N) Γ

  data NComp : (N : CTy) (Γ : Cxt) → Set where
    ret   : ∀{Γ P}   (v : NVal P Γ)                → NComp (comp P) Γ
    rec   : ∀{Γ I N} (t : ∀ i → NComp (N i) Γ)     → NComp (Π I N) Γ
    abs   : ∀{Γ P N} (t : NComp N (P ∷ Γ))         → NComp (P ⇒ N) Γ
    split : ∀{Γ P₁ P₂ N} (x : (P₁ ×̇ P₂) ∈ Γ) (t : NComp N (P₂ ∷ P₁ ∷ Γ)) → NComp N Γ
    case  : ∀{Γ I P N} (x : Σ̇ I P ∈ Γ) (t : ∀ i → NComp N (P i ∷ Γ)) → NComp N Γ
