{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

module CBVNTranslations where

open import Library
open import Polarized

-- Intuitionistic propositional logic

data IPL : Set where
  Atom        : (P : Atoms) → IPL
  True False  : IPL
  _∨_ _∧_ _⇒_ : (A B : IPL) → IPL

module CallByName where

  _⁻ : IPL → Form -
  Atom P ⁻  = Atom- P
  True ⁻    = True
  False ⁻   = Comp False
  (A ∨ B) ⁻ = Comp (Thunk (A ⁻) ∨ Thunk (B ⁻))
  (A ∧ B) ⁻ = A ⁻ ∧ B ⁻
  (A ⇒ B) ⁻ = Thunk (A ⁻) ⇒ B ⁻

module CallByValue where

  _⁺ : IPL → Form +
  Atom P ⁺  = Atom P
  True ⁺    = True
  False ⁺   = False
  (A ∨ B) ⁺ = A ⁺ ∨ B ⁺
  (A ∧ B) ⁺ = A ⁺ ∧ B ⁺
  (A ⇒ B) ⁺ = Thunk (A ⁺ ⇒ Comp (B ⁺))

mutual

  _⁺ : IPL → Form +
  Atom P ⁺  = Atom P
  True ⁺    = True
  False ⁺   = False
  (A ∨ B) ⁺ = A ⁺ ∨ B ⁺
  (A ∧ B) ⁺ = A ⁺ ∧ B ⁺
  (A ⇒ B) ⁺ = Thunk (A ⁺ ⇒ B ⁻)

  _⁻ : IPL → Form -
  Atom P ⁻  = Atom- P
  True ⁻    = True
  False ⁻   = Comp False
  (A ∨ B) ⁻ = Comp (A ⁺ ∨ B ⁺)
  (A ∧ B) ⁻ = A ⁻ ∧ B ⁻
  (A ⇒ B) ⁻ = A ⁺ ⇒ B ⁻

-- Derivations

infix 2 _⊢_

data _⊢_ (Γ : Cxt' IPL) : (A : IPL) → Set where
  hyp    : ∀{A} (x : Hyp' IPL A Γ) → Γ ⊢ A
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

Tm = λ A Γ → Γ ⊢ A

-- Call-by value evaluation

module CBV where

  V⟦_⟧ = λ A → ⟦ A ⁺ ⟧
  C⟦_⟧ = λ A → ⟦ A ⁻ ⟧

  return : ∀ A → V⟦ A ⟧ →̇ C⟦ A ⟧
  return (Atom P) v = returnC v
  return True v = v
  return False v = returnC v
  return (A ∨ B) v = returnC v
  return (A ∧ B) (a , b) = return A a , return B b
  return (A ⇒ B) v = v

  run : ∀ A → C⟦ A ⟧ →̇ Cover ∞ ∞ V⟦ A ⟧
  run (Atom P) c = c
  run True c = returnC c
  run False c = c
  run (A ∨ B) c = c
  run (A ∧ B) c = joinCover (mapCover' (λ τ a → mapCover' (λ τ' b → (mon⟦ A ⁺ ⟧ τ' a , b)) (run B (mon⟦ B ⁻ ⟧ τ (proj₂ c)))) (run A (proj₁ c)))
  run (A ⇒ B) c = returnC c

  -- Fundamental theorem
  -- Extension of ⟦_⟧ to contexts

  G⟦_⟧ : ∀ (Γ : Cxt' IPL) (Δ : Cxt) → Set
  G⟦ ε     ⟧ Δ = ⊤
  G⟦ Γ ∙ A ⟧ Δ = G⟦ Γ ⟧ Δ × V⟦ A ⟧ Δ

  -- monG : ∀{Γ Δ Φ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ → G⟦ Γ ⟧ Φ

  monG : ∀{Γ} → Mon G⟦ Γ ⟧
  monG {ε} τ _ = _
  monG {Γ ∙ A} τ (γ , a) = monG τ γ , mon⟦ A ⁺ ⟧ τ a

  -- Variable case.

  lookup : ∀{Γ A} (x : Hyp' IPL A Γ) → G⟦ Γ ⟧ →̇ V⟦ A ⟧
  lookup top     = proj₂
  lookup (pop x) = lookup x ∘ proj₁

  impIntro : ∀ {A B Γ} (f : KFun (Cover ∞ ∞ ⟦ A ⟧) ⟦ B ⟧ Γ) → ⟦ A ⇒ B ⟧ Γ
  impIntro f τ a = f τ (returnC a)

  -- impElim : ∀ A B {Γ} → (f : C⟦ A ⇒ B ⟧ Γ) (a : C⟦ A ⟧ Γ) → C⟦ B ⟧ Γ
  -- impElim (Atom P) B f = paste (B ⁻) ∘ mapCover' f
  -- impElim False B f = paste (B ⁻) ∘ mapCover' f
  -- impElim True B f = f id≤
  -- impElim (A ∨ A₁) B f = paste (B ⁻) ∘ mapCover' f
  -- impElim (A ∧ A₁) B f = {!paste (B ⁻) ∘ mapCover' f!}
  -- impElim (A ⇒ A₁) B f = f id≤

  impElim : ∀ A B {Γ} → (f : C⟦ A ⇒ B ⟧ Γ) (a : C⟦ A ⟧ Γ) → C⟦ B ⟧ Γ
  impElim A B f a = paste (B ⁻) (mapCover' f (run A a))

  -- A lemma for the orE case.

  orElim : ∀ A B C {Γ} → C⟦ A ∨ B ⟧ Γ → C⟦ A ⇒ C ⟧ Γ → C⟦ B ⇒ C ⟧ Γ → C⟦ C ⟧ Γ
  orElim A B C c g h = paste (C ⁻) (mapCover' (λ τ → [ g τ , h τ ]) c)

  -- A lemma for the falseE case.

  -- Casts an empty cover into any semantic value (by contradiction).

  falseElim : ∀ C → C⟦ False ⟧ →̇ C⟦ C ⟧
  falseElim C = paste (C ⁻) ∘ mapCover ⊥-elim

  -- The fundamental theorem
  eval :  ∀{A Γ} (t : Γ ⊢ A) → G⟦ Γ ⟧ →̇ C⟦ A ⟧
  eval {A} (hyp x)           = return A ∘ lookup x
  eval (impI t)    γ τ a     = eval t (monG τ γ , a)
  eval (impE {A} {B} t u)  γ = impElim A B (eval t γ) (eval u γ)
  eval (andI t u)  γ         = eval t γ , eval u γ
  eval (andE₁ t)             = proj₁ ∘ eval t
  eval (andE₂ t)             = proj₂ ∘ eval t
  eval (orI₁ {A} {B} t) γ    = mapCover inj₁ (run A (eval t γ))
  eval (orI₂ {A} {B} t) γ    = mapCover inj₂ (run B (eval t γ))
  eval (orE {A} {B} {C} t u v) γ = orElim A B C (eval t γ)
    (λ τ a → eval u (monG τ γ , a))
    (λ τ b → eval v (monG τ γ , b))
  eval {C} (falseE t) γ      = falseElim C (eval t γ)
  eval trueI       γ         = _

  _⁺⁺ : (Γ : Cxt' IPL) → Cxt
  ε ⁺⁺ = ε
  (Γ ∙ A) ⁺⁺ = Γ ⁺⁺ ∙ A ⁻

  -- Identity environment

  ide : ∀ Γ → Cover ∞ ∞ G⟦ Γ ⟧ (Γ ⁺⁺)
  ide ε = returnC _
  ide (Γ ∙ A) = {!!}
    -- monG (weak id≤) (ide Γ) , {! reflectHyp (A ⁺) (λ τ a → a) !}
{-
  -- Normalization

  norm : ∀{A : IPL} {Γ : Cxt' IPL} → Tm A Γ → RInv (Γ ⁺⁺) (A ⁻)
  norm t = reify- _ (eval t (ide _))


-- -}
-- -}
