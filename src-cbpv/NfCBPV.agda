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

  -- Right non-invertible

  data Val' : (P : VTy) (Γ : Cxt) → Set where
    var   : ∀{Γ P}     (x : P ∈ Γ)                       → Val' P Γ
    pair  : ∀{Γ P₁ P₂} (v₁ : Val' P₁ Γ) (v₂ : Val' P₂ Γ) → Val' (P₁ ×̇ P₂) Γ
    inj   : ∀{Γ I P} i (v : Val' (P i) Γ)                → Val' (Σ̇ I P) Γ
    thunk : ∀{Γ N}     (t : Comp N Γ)                    → Val' (thunk N) Γ

mutual

  Val = Val' Comp

  data Comp : (N : CTy) (Γ : Cxt) → Set where
    -- introductions
    ret   : ∀{Γ P}       (v : Val P Γ)                → Comp (comp P) Γ
    rec   : ∀{Γ I N}     (t : ∀ i → Comp (N i) Γ)     → Comp (Π I N) Γ
    abs   : ∀{Γ P N}     (t : Comp N (P ∷ Γ))         → Comp (P ⇒ N) Γ
    -- positive eliminations
    split : ∀{Γ P₁ P₂ N} (v : Val (P₁ ×̇ P₂) Γ) (t : Comp N (P₂ ∷ P₁ ∷ Γ)) → Comp N Γ
    case  : ∀{Γ I P N}   (v : Val (Σ̇ I P) Γ) (t : ∀ i → Comp N (P i ∷ Γ)) → Comp N Γ
    bind  : ∀{Γ P N}     (u : Comp (comp P) Γ) (t : Comp N (P ∷ Γ)) → Comp N Γ
    -- negative elimination
    force : ∀{Γ N}       (v : Val (thunk N) Γ)   → Comp N Γ
    prj   : ∀{Γ I N} i   (t : Comp (Π I N) Γ)                        → Comp (N i) Γ
    app   : ∀{Γ P N}     (t : Comp (P ⇒ N) Γ)   (v : Val P Γ)        → Comp N Γ
    -- cut
    letv  : ∀{Γ P N}     (v : Val P Γ)         (t : Comp N (P ∷ Γ)) → Comp N Γ

-- Normal forms

module _ (Val : VTy → Cxt → Set) where

  -- Right non-invertible

  data Ne' : (N : CTy) (Γ : Cxt) → Set where
    force : ∀{Γ N}     (x : thunk N ∈ Γ)                 → Ne' N Γ
    prj   : ∀{Γ I N} i (t : Ne' (Π I N) Γ)               → Ne' (N i) Γ
    app   : ∀{Γ P N}   (t : Ne' (P ⇒ N) Γ) (v : Val P Γ) → Ne' N Γ

mutual

  NVal = Val' Nf
  Ne   = Ne' NVal

  data NComp : (Q : VTy) (Γ : Cxt) → Set where
    ret   : ∀{Γ Q}       (v : NVal Q Γ)      → NComp Q Γ   -- Invoke RFoc
    ne    : ∀{Γ Q}       (n : Ne (comp Q) Γ) → NComp Q Γ   -- Finish with LFoc
      -- e.g. app (force f) x

    -- Use lemma LFoc
    bind  : ∀{Γ P Q}     (u : Ne (comp P) Γ) (t : NComp Q (P ∷ Γ)) → NComp Q Γ

    -- Left invertible
    split : ∀{Γ P₁ P₂ Q} (x : (P₁ ×̇ P₂) ∈ Γ) (t : NComp Q (P₂ ∷ P₁ ∷ Γ)) → NComp Q Γ
    case  : ∀{Γ I P Q}   (x : Σ̇ I P ∈ Γ)     (t : ∀ i → NComp Q (P i ∷ Γ)) → NComp Q Γ

  -- Right invertible

  data Nf : (N : CTy) (Γ : Cxt) → Set where
    comp  : ∀{Γ P}   (t : NComp P Γ)        → Nf (comp P) Γ
    rec   : ∀{Γ I N} (t : ∀ i → Nf (N i) Γ) → Nf (Π I N) Γ
    abs   : ∀{Γ P N} (t : Nf N (P ∷ Γ))     → Nf (P ⇒ N) Γ
