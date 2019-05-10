---------------------------------------------------------------------------
-- Normalization by Evaluation for Intuitionistic Propositional Logic
--
-- We employ a monadic interpreter for the soundness part,
-- and a special class of monads, called cover monads,
-- for the completeness part.
--
-- Normalization is completeness after soundness.
--
-- We give two instances of a cover monad: the free cover monad
-- and the continuation monad with normal forms as answer type.
---------------------------------------------------------------------------

{-# OPTIONS --postfix-projections #-}

open import Library

module NfModelMonad (Base : Set) where

import Formulas   ; open module Form = Formulas    Base
import Derivations; open module Der  = Derivations Base

---------------------------------------------------------------------------
-- Specification of a strong monad on presheaves.
-- Devoid of monad laws.

record Monad : Set₁ where

  -- Presheaf transformer.

  field
    C     : (P : Cxt → Set) (Γ : Cxt) → Set
    monC  : ∀{P} (monP : Mon P) → Mon (C P)

  -- Strong functor.

  field
    mapC' : ∀{P Q} → ⟨ P ⇒̂ Q ⊙ C P ⟩→̇ C Q

  -- Ordinary functor: an instance of mapC'.

  mapC : ∀{P Q} → (P →̇ Q) → (C P →̇ C Q)
  mapC f = mapC' λ τ → f

  -- Monad.

  field
    return : ∀{P} (monP : Mon P) → P →̇ C P
    joinC  : ∀{P} → C (C P) →̇ C P

  -- Kleisli extension.

  extC : ∀{P Q} → (P →̇ C Q) → C P →̇ C Q
  extC f = joinC ∘ mapC f

  -- Strong bind.

  bindC' : ∀{P Q} (monP : Mon P) → C P →̇ (P ⇒̂ C Q) ⇒̂ C Q
  bindC' monP c τ k = joinC (mapC' k (monC monP τ c))

---------------------------------------------------------------------------
-- A model of IPL parametrized by a strong monad.

module Soundness (monad : Monad) (open Monad monad) where

  -- The negative connectives True, ∧, and ⇒ are explained as usual by η-expansion
  -- and the meta-level connective.

  -- The positive connectives False and ∨ are inhabited by case trees.
  -- In case False, the tree has no leaves.
  -- In case A ∨ B, each leaf must be in the semantics of either A or B.

  T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
  T⟦ Atom P ⟧   = C (Ne' (Atom P))
  T⟦ False  ⟧   = C λ Δ → ⊥
  T⟦ A ∨ B  ⟧   = C λ Δ → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ
  T⟦ True   ⟧ Γ = ⊤
  T⟦ A ∧ B  ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
  T⟦ A ⇒ B  ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ B ⟧ Δ

  -- Monotonicity of the model is proven by induction on the proposition,
  -- using monotonicity of covers and the built-in monotonicity at implication.

  -- monT : ∀ A {Γ Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ → T⟦ A ⟧ Δ

  monFalse : Mon (λ Γ → ⊥)
  monFalse τ ()

  mutual
    monT : ∀ A → Mon T⟦ A ⟧
    monT (Atom P)          = monC monNe
    monT False             = monC monFalse
    monT (A ∨ B)           = monC (monOr A B)
    monT True              = _
    monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
    monT (A ⇒ B) τ f σ     = f (σ • τ)

    monOr : ∀ A B → Mon (λ Γ → T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ)
    monOr A B τ = map-⊎ (monT A τ) (monT B τ)

  returnOr : ∀ A B {Γ} → T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ → T⟦ A ∨ B ⟧ Γ
  returnOr A B = return (monOr A B)

  -- We can run computations of semantic values.
  -- This replaces the paste (weak sheaf condition) of Beth models.

  run : ∀ A → C T⟦ A ⟧ →̇ T⟦ A ⟧
  run (Atom P)      = joinC
  run False         = joinC
  run (A ∨ B)       = joinC
  run True          = _
  run (A ∧ B)       = < run A ∘ mapC proj₁ , run B ∘ mapC proj₂  >
  run (A ⇒ B) c τ a = run B $ mapC' (λ δ f → f id≤ (monT A δ a)) $ monC (monT (A ⇒ B)) τ c

  -- Remark: A variant of run in the style of bind.

  run' : ∀ {P} (monP : Mon P) A → C P →̇ (P ⇒̂ T⟦ A ⟧) ⇒̂ T⟦ A ⟧
  run' monP (Atom p)          = bindC' monP
  run' monP False             = bindC' monP
  run' monP (A ∨ B)           = bindC' monP
  run' monP True              = _
  run' monP (A ∧ B) c τ k     = run' monP A c τ (λ σ → proj₁ ∘ k σ) , run' monP B c τ (λ σ → proj₂ ∘ k σ)
  run' monP (A ⇒ B) c τ k σ a = run' monP B c (σ • τ) λ σ' p → k (σ' • σ) p id≤ (monT A σ' a)

  -- Fundamental theorem (interpretation / soundness).

  -- Pointwise extension of T⟦_⟧ to contexts.

  G⟦_⟧ : ∀ (Γ Δ : Cxt) → Set
  G⟦ ε     ⟧ Δ = ⊤
  G⟦ Γ ∙ A ⟧ Δ = G⟦ Γ ⟧ Δ × T⟦ A ⟧ Δ

  -- monG : ∀{Γ Δ Φ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ → G⟦ Γ ⟧ Φ

  monG : ∀{Γ} → Mon G⟦ Γ ⟧
  monG {ε}     τ _       = _
  monG {Γ ∙ A} τ (γ , a) = monG τ γ , monT A τ a

  -- Variable case.

  lookup : ∀{Γ A} (x : Hyp A Γ) → G⟦ Γ ⟧ →̇ T⟦ A ⟧
  lookup top     = proj₂
  lookup (pop x) = lookup x ∘ proj₁

  -- A lemma for the orE case.

  orElim : ∀ A B C → ⟨ T⟦ A ∨ B ⟧ ⊙ T⟦ A ⇒ C ⟧ ⊙ T⟦ B ⇒ C ⟧ ⟩→̇ T⟦ C ⟧
  orElim A B C c g h = run C (mapC' (λ τ → [ g τ , h τ ]) c)

  orElim' : ∀ A B C → ⟨ T⟦ A ∨ B ⟧ ⊙ T⟦ A ⇒ C ⟧ ⊙ T⟦ B ⇒ C ⟧ ⟩→̇ T⟦ C ⟧
  orElim' A B C c g h = run' (monOr A B) C c id≤ λ τ → [ g τ , h τ ]

  -- A lemma for the falseE case.
  -- Casts an empty cover into any semantic value (by contradiction).

  falseElim : ∀ C → T⟦ False ⟧ →̇ T⟦ C ⟧
  falseElim C = run C ∘ mapC ⊥-elim

  -- The fundamental theorem

  eval :  ∀{A Γ} (t : Γ ⊢ A) → G⟦ Γ ⟧ →̇ T⟦ A ⟧
  eval (hyp x)           = lookup x
  eval (impI t)    γ τ a = eval t (monG τ γ , a)
  eval (impE t u)  γ     = eval t γ id≤ (eval u γ)
  eval (andI t u)  γ     = eval t γ , eval u γ
  eval (andE₁ t)         = proj₁ ∘ eval t
  eval (andE₂ t)         = proj₂ ∘ eval t
  eval (orI₁ {A} {B} t) γ = returnOr A B (inj₁ (eval t γ))
  eval (orI₂ {A} {B} t) γ = returnOr A B (inj₂ (eval t γ))
  eval (orE {A = A} {B} {C} t u v) γ = orElim A B C (eval t γ)
    (λ τ a → eval u (monG τ γ , a))
    (λ τ b → eval v (monG τ γ , b))
  eval {C} (falseE t) γ  = falseElim C (eval t γ)
  eval trueI       γ     = _

---------------------------------------------------------------------------
-- A strong monad with services to provide a cover.
-- Devoid of laws.

record CoverMonad : Set₁ where
  field
    monad : Monad
  open Monad monad public renaming (C to Cover)

  -- Services for case distinction.

  field
    falseC  : ∀{P} → Ne' False →̇ Cover P
    orC     : ∀{P Γ C D} (t : Ne Γ (C ∨ D))
                (c : Cover P (Γ ∙ C))
                (d : Cover P (Γ ∙ D)) → Cover P Γ

  -- Service for reification of into case trees.

  field
    runNf : ∀{A} → Cover (Nf' A) →̇ Nf' A

  -- A continuation version of runNf.

  runNf' : ∀ {A P} (monP : Mon P) → Cover P →̇ (P ⇒̂ Nf' A) ⇒̂ Nf' A
  runNf' monP c τ k = runNf (mapC' k (monC monP τ c))

---------------------------------------------------------------------------
-- Completeness of IPL via a cover monad.

module Completeness (covM : CoverMonad) (open CoverMonad covM) where
  open Soundness monad

  -- Reflection / reification, proven simultaneously by induction on the proposition.

  -- Reflection is η-expansion (and recursively reflection);
  -- at positive connections we build a case tree with a single scrutinee: the neutral
  -- we are reflecting.

  -- At implication, we need reification, which produces introductions
  -- and reifies the stored case trees.

  mutual

    fresh : ∀ {Γ} A → T⟦ A ⟧ (Γ ∙ A)
    fresh A = reflect A (hyp top)

    reflect : ∀ A → Ne' A →̇ T⟦ A ⟧
    reflect (Atom P) t     = return monNe t
    reflect False    t     = falseC t
    reflect (A ∨ B)  t     = orC t (returnOr A B (inj₁ (fresh A)))
                                   (returnOr A B (inj₂ (fresh B)))
    reflect True     t     = _
    reflect (A ∧ B)  t     = reflect A (andE₁ t) , reflect B (andE₂ t)
    reflect (A ⇒ B)  t τ a = reflect B (impE (monNe τ t) (reify A a))

    reify : ∀ A → T⟦ A ⟧ →̇ Nf' A
    reify (Atom P)        = runNf ∘ mapC ne
    reify False           = runNf ∘ mapC ⊥-elim
    reify (A ∨ B)         = runNf ∘ mapC [ orI₁ ∘ reify A , orI₂ ∘ reify B ]
    reify True _          = trueI
    reify (A ∧ B) (a , b) = andI (reify A a) (reify B b)
    reify (A ⇒ B) ⟦f⟧     = impI (reify B (⟦f⟧ (weak id≤) (fresh A)))

---------------------------------------------------------------------------
-- Normalization is completeness (reification) after soundness (evaluation)

module Normalization (covM : CoverMonad) (open CoverMonad covM) where
  open Soundness monad
  open Completeness covM

  -- Identity environment, constructed by reflection.

  freshG : ∀ Γ → G⟦ Γ ⟧ Γ
  freshG ε       = _
  freshG (Γ ∙ A) = monG (weak id≤) (freshG Γ) , fresh A

  -- A variant (no improvement).

  freshG' : ∀ Γ {Δ} (τ : Δ ≤ Γ) → G⟦ Γ ⟧ Δ
  freshG' ε       τ = _
  freshG' (Γ ∙ A) τ = freshG' Γ (τ • weak id≤) , monT A τ (fresh A)

  -- Normalization

  norm : ∀{A} → Tm A →̇ Nf' A
  norm t = reify _ (eval t (freshG _))

---------------------------------------------------------------------------
-- Case tree instance of cover monad

module CaseTree where

  data Cover (P : Cxt → Set) (Γ : Cxt) : Set where
    returnC : (p : P Γ) → Cover P Γ
    falseC  : (t : Ne Γ False) → Cover P Γ
    orC     : ∀{C D} (t : Ne Γ (C ∨ D))
                (c : Cover P (Γ ∙ C))
                (d : Cover P (Γ ∙ D)) → Cover P Γ

  return : ∀{P} (monP : Mon P) → P →̇ Cover P
  return monP p = returnC p

  -- Syntactic paste.

  runNf : ∀{A} → Cover (Nf' A) →̇ Nf' A
  runNf (returnC p) = p
  runNf (falseC t)  = falseE t
  runNf (orC t c d) = orE t (runNf c) (runNf d)

  -- Weakening covers:  A case tree in Γ can be transported to a thinning Δ
  -- by weakening all the scrutinees.

  monC : ∀{P} → (monP : Mon P) → Mon (Cover P)
  monC monP τ (returnC p) = returnC (monP τ p)
  monC monP τ (falseC t)  = falseC (monNe τ t)
  monC monP τ (orC t c d) = orC (monNe τ t) (monC monP (lift τ) c)
                                            (monC monP (lift τ) d)
  -- Monad.

  mapC : ∀{P Q} → (P →̇ Q) → (Cover P →̇ Cover Q)
  mapC f (returnC p) = returnC (f p)
  mapC f (falseC t)  = falseC t
  mapC f (orC t c d) = orC t (mapC f c) (mapC f d)

  joinC : ∀{P} → Cover (Cover P) →̇ Cover P
  joinC (returnC p) = p
  joinC (falseC t)  = falseC t
  joinC (orC t c d) = orC t (joinC c) (joinC d)

  -- Strong functoriality.

  mapC' : ∀{P Q Γ} → KFun P Q Γ → Cover P Γ → Cover Q Γ
  mapC' f (returnC p) = returnC (f id≤ p)
  mapC' f (falseC t)  = falseC t
  mapC' f (orC t c d) = orC t (mapC' (λ τ → f (τ • weak id≤)) c)
                              (mapC' (λ τ → f (τ • weak id≤)) d)

caseTreeMonad : CoverMonad
caseTreeMonad = record {monad = record{CaseTree}; CaseTree}

-- A normalization function using case trees.

open Normalization caseTreeMonad using () renaming (norm to normCaseTree)

---------------------------------------------------------------------------
-- Continuation instance of cover monad

module Continuation where

  record Cover (P : Cxt → Set) (Γ : Cxt) : Set where
    field runNf' : ∀ {A} → ((P ⇒̂ Nf' A) ⇒̂ Nf' A) Γ
  open Cover

  -- Services.

  runNf : ∀{A} → Cover (Nf' A) →̇ Nf' A
  runNf {A} {Γ} c = c .runNf' id≤ (λ τ → id)

  falseC : ∀{P} → Ne' False →̇ Cover P
  falseC t .runNf' τ k = falseE (monNe τ t)

  orC : ∀{P Γ C D} (t : Ne Γ (C ∨ D))
          (c : Cover P (Γ ∙ C))
          (d : Cover P (Γ ∙ D)) → Cover P Γ

  orC t c d .runNf' τ k = orE (monNe τ t)
    (c .runNf' (lift τ) (λ δ → k (δ • weak id≤)))
    (d .runNf' (lift τ) (λ δ → k (δ • weak id≤)))

  -- Monad infrastructure.

  monC : ∀{P} → (monP : Mon P) → Mon (Cover P)
  monC monP τ c .runNf' τ₁ k = c .runNf' (τ₁ • τ) k

  mapC' : ∀{P Q} → ⟨ P ⇒̂ Q ⊙ Cover P ⟩→̇ Cover Q
  mapC' k c .runNf' τ l = c .runNf' τ λ δ p → l δ (k (δ • τ) p)

  mapC : ∀{P Q} → (P →̇ Q) → (Cover P →̇ Cover Q)
  mapC f = mapC' λ τ → f

  return : ∀{P} (monP : Mon P) → P →̇ Cover P
  return monP p .runNf' τ k = k id≤ (monP τ p)

  joinC : ∀{P} → Cover (Cover P) →̇ Cover P
  joinC c .runNf' τ k = c .runNf' τ λ δ c' → c' .runNf' id≤ λ δ' → k (δ' • δ)

  extC : ∀{P Q} → (P →̇ Cover Q) → Cover P →̇ Cover Q
  extC f = joinC ∘ mapC f

  bindC' : ∀{P Q} → Cover P →̇ (P ⇒̂ Cover Q) ⇒̂ Cover Q
  bindC' c τ k .runNf' τ' k' = c .runNf' (τ' • τ) λ σ p → k (σ • τ') p .runNf' id≤ λ σ' → k' (σ' • σ)

continuationMonad : CoverMonad
continuationMonad = record{monad = record{Continuation}; Continuation}

-- A normalization function using continuations.

open Normalization continuationMonad using () renaming (norm to normContinuation)

-- Q.E.D.

-- -}
-- -}
-- -}
