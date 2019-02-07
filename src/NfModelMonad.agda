-- A Beth model of normal forms

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS -v rewriting:90 #-}

open import Library

module NfModelMonad (Base : Set) where

import Formulas   ; open module Form = Formulas    Base
import Derivations; open module Der  = Derivations Base

-- Beth model

record CoverMonad : Set₁ where

  -- Presheaf transformer

  field
    Cover   : (P : Cxt → Set) (Γ : Cxt) → Set
    monC    : ∀{P} → (monP : Mon P) → Mon (Cover P)

  -- Strong functor

  field
    mapC'   : ∀{P Q} → ⟨ P ⇒̂ Q ⊙ Cover P ⟩→̇ Cover Q

  mapC : ∀{P Q} → (P →̇ Q) → (Cover P →̇ Cover Q)
  mapC f = mapC' λ τ → f

  -- Monad

  field
    return : ∀{P} (monP : Mon P) → P →̇ Cover P
    joinC : ∀{P} → Cover (Cover P) →̇ Cover P

  -- Kleisli extension

  extC : ∀{P Q} → (P →̇ Cover Q) → Cover P →̇ Cover Q
  extC f = joinC ∘ mapC f

  -- Strong bind

  bindC' : ∀{P Q} (monP : Mon P) → Cover P →̇ (P ⇒̂ Cover Q) ⇒̂ Cover Q
  bindC' monP c τ k = joinC (mapC' k (monC monP τ c))

  -- Services

  field
    falseC  : ∀{P} → Ne' False →̇ Cover P
    orC     : ∀{P Γ C D} (t : Ne Γ (C ∨ D))
                (c : Cover P (Γ ∙ C))
                (d : Cover P (Γ ∙ D)) → Cover P Γ
  field
    runNf : ∀{A} → Cover (Nf' A) →̇ Nf' A

  -- A continuation version of runNf

  runNf' : ∀ {A P} (monP : Mon P) → Cover P →̇ (P ⇒̂ Nf' A) ⇒̂ Nf' A
  runNf' monP c τ k = runNf (mapC' k (monC monP τ c))


module Beth (covM : CoverMonad) (open CoverMonad covM) where

  -- The syntactic Beth model.

  -- We interpret base propositions  Atom P  by their normal deriviations.
  -- ("Normal" is important; "neutral is not sufficient since we need case trees here.)

  -- The negative connectives True, ∧, and ⇒ are explained as usual by η-expansion
  -- and the meta-level connective.

  -- The positive connectives False and ∨ are inhabited by case trees.
  -- In case False, the tree has no leaves.
  -- In case A ∨ B, each leaf must be in the semantics of either A or B.

  T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
  T⟦ Atom P ⟧ = Nf' (Atom P)
  T⟦ True   ⟧ Γ = ⊤
  T⟦ False  ⟧ = Cover λ Δ → ⊥
  T⟦ A ∨ B  ⟧ = Cover λ Δ → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ
  T⟦ A ∧ B  ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
  T⟦ A ⇒ B  ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ B ⟧ Δ

  -- Monotonicity of the model is proven by induction on the proposition,
  -- using monotonicity of covers and the built-in monotonicity at implication.

  -- monT : ∀ A {Γ Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ → T⟦ A ⟧ Δ

  monFalse : Mon (λ Γ → ⊥)
  monFalse τ ()

  mutual
    monT : ∀ A → Mon T⟦ A ⟧
    monT (Atom P) = monNf
    monT True     = _
    monT False    = monC λ τ ()
    monT (A ∨ B)  = monC (monOr A B)
    monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
    monT (A ⇒ B) τ f σ = f (σ • τ)

    monOr : ∀ A B → Mon (λ Γ → T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ)
    monOr A B τ = map-⊎ (monT A τ) (monT B τ)

  returnOr : ∀ A B {Γ} → T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ → T⟦ A ∨ B ⟧ Γ
  returnOr A B = return (monOr A B)

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
    reflect (Atom P) t = ne t
    reflect True     t = _
    reflect False    t = falseC t
    reflect (A ∨ B)  t = orC t (returnOr A B (inj₁ (fresh A)))
                               (returnOr A B (inj₂ (fresh B)))
    reflect (A ∧ B)  t = reflect A (andE₁ t) , reflect B (andE₂ t)
    reflect (A ⇒ B)  t τ a = reflect B (impE (monNe τ t) (reify A a))

    reify : ∀ A → T⟦ A ⟧ →̇ Nf' A
    reify (Atom P) t      = t
    reify True _          = trueI
    reify False           = runNf ∘ mapC ⊥-elim
    reify (A ∨ B)         = runNf ∘ mapC [ orI₁ ∘ reify A , orI₂ ∘ reify B ]
    reify (A ∧ B) (a , b) = andI (reify A a) (reify B b)
    reify (A ⇒ B) ⟦f⟧     = impI (reify B (⟦f⟧ (weak id≤) (fresh A)))

  -- Semantic paste.  (Sheaf condition -- algorithmic part.)

  run : ∀ A → Cover T⟦ A ⟧ →̇ T⟦ A ⟧
  run (Atom P) = runNf
  run True     = _
  run False    = joinC
  run (A ∨ B)  = joinC
  run (A ∧ B)  = < run A ∘ mapC proj₁ , run B ∘ mapC proj₂  >
  run (A ⇒ B) c τ a = run B $ mapC' (λ δ f → f id≤ (monT A δ a)) $ monC (monT (A ⇒ B)) τ c

  run' : ∀ {P} (monP : Mon P) A → Cover P →̇ (P ⇒̂ T⟦ A ⟧) ⇒̂ T⟦ A ⟧
  run' monP (Atom p) = runNf' monP
  run' monP True     = λ _ _ _ → _
  run' monP False    = bindC' monP
  run' monP (A ∨ B)  = bindC' monP
  run' monP (A ∧ B) c τ k     = run' monP A c τ (λ σ → proj₁ ∘ k σ) , run' monP B c τ (λ σ → proj₂ ∘ k σ)
  run' monP (A ⇒ B) c τ k σ a = run' monP B c (σ • τ) λ σ' p → k (σ' • σ) p id≤ (monT A σ' a)

  -- Fundamental theorem
  -- Extension of T⟦_⟧ to contexts

  G⟦_⟧ : ∀ (Γ Δ : Cxt) → Set
  G⟦ ε     ⟧ Δ = ⊤
  G⟦ Γ ∙ A ⟧ Δ = G⟦ Γ ⟧ Δ × T⟦ A ⟧ Δ

  -- monG : ∀{Γ Δ Φ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ → G⟦ Γ ⟧ Φ

  monG : ∀{Γ} → Mon G⟦ Γ ⟧
  monG {ε} τ _ = _
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

  falseElim' : ∀ C → T⟦ False ⟧ →̇ T⟦ C ⟧
  falseElim' C c =  run' monFalse C c id≤ λ τ → ⊥-elim

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

  -- Identity environment

  ide : ∀ Γ → G⟦ Γ ⟧ Γ
  ide ε = _
  ide (Γ ∙ A) = monG (weak id≤) (ide Γ) , reflect A (hyp top)

  -- Normalization

  norm : ∀{A} → Tm A →̇ Nf' A
  norm t = reify _ (eval t (ide _))

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

  -- Syntactic paste

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

  -- Monad

  mapC : ∀{P Q} → (P →̇ Q) → (Cover P →̇ Cover Q)
  mapC f (returnC p) = returnC (f p)
  mapC f (falseC t)  = falseC t
  mapC f (orC t c d) = orC t (mapC f c) (mapC f d)

  joinC : ∀{P} → Cover (Cover P) →̇ Cover P
  joinC (returnC p) = p
  joinC (falseC t)  = falseC t
  joinC (orC t c d) = orC t (joinC c) (joinC d)

  -- Strong functoriality

  mapC' : ∀{P Q Γ} → KFun P Q Γ → Cover P Γ → Cover Q Γ
  mapC' f (returnC p) = returnC (f id≤ p)
  mapC' f (falseC t)  = falseC t
  mapC' f (orC t c d) = orC t (mapC' (λ τ → f (τ • weak id≤)) c)
                              (mapC' (λ τ → f (τ • weak id≤)) d)

caseTreeMonad : CoverMonad
caseTreeMonad = record {CaseTree}

-- Continuation instance of cover monad

module Continuation where

  record Cover (P : Cxt → Set) (Γ : Cxt) : Set where
    field runNf' : ∀ {A} → ((P ⇒̂ Nf' A) ⇒̂ Nf' A) Γ
  open Cover

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
continuationMonad = record{Continuation}

-- Q.E.D. -}
-- -}
-- -}
