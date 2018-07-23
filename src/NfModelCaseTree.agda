-- A Beth model of normal forms
-- Version presented at the Initial Types Club, 2018-07-19

open import Library

module NfModelCaseTree (Base : Set) where

import Formulas   ; open module Form = Formulas    Base
import Derivations; open module Der  = Derivations Base

-- Beth model

data Cover (P : Cxt → Set) (Γ : Cxt) : Set where
  returnC : (p : P Γ) → Cover P Γ
  falseC  : (t : Ne Γ False) → Cover P Γ
  orC     : ∀{C D} (t : Ne Γ (C ∨ D))
              (c : Cover P (Γ ∙ C))
              (d : Cover P (Γ ∙ D)) → Cover P Γ

-- Syntactic paste

pasteNf : ∀{A} → Cover (Nf' A) →̇ Nf' A
pasteNf (returnC p) = p
pasteNf (falseC t)  = falseE t
pasteNf (orC t c d) = orE t (pasteNf c) (pasteNf d)

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

-- Version of mapC with f relativized to thinnings of Γ

mapC' : ∀{P Q Γ} → KFun P Q Γ → Cover P Γ → Cover Q Γ
mapC' f (returnC p) = returnC (f id≤ p)
mapC' f (falseC t)  = falseC t
mapC' f (orC t c d) = orC t (mapC' (λ τ → f (τ • weak id≤)) c)
                            (mapC' (λ τ → f (τ • weak id≤)) d)

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

monT : ∀ A → Mon T⟦ A ⟧
monT (Atom P) = monNf
monT True     = _
monT False    = monC λ τ ()
monT (A ∨ B)  = monC λ τ → map-⊎ (monT A τ) (monT B τ)
monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
monT (A ⇒ B) τ f σ = f (σ • τ)

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
  reflect (A ∨ B)  t = orC t (returnC (inj₁ (fresh A)))
                             (returnC (inj₂ (fresh B)))
  reflect (A ∧ B)  t = reflect A (andE₁ t) , reflect B (andE₂ t)
  reflect (A ⇒ B)  t τ a = reflect B (impE (monNe τ t) (reify A a))

  reify : ∀ A → T⟦ A ⟧ →̇ Nf' A
  reify (Atom P) t      = t
  reify True _          = trueI
  reify False           = pasteNf ∘  mapC ⊥-elim
  reify (A ∨ B)         = pasteNf ∘  mapC [ orI₁ ∘ reify A , orI₂ ∘ reify B ]
  reify (A ∧ B) (a , b) = andI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = impI (reify B (⟦f⟧ (weak id≤) (fresh A)))

-- Semantic paste.

paste : ∀ A → Cover T⟦ A ⟧ →̇ T⟦ A ⟧
paste (Atom P) = pasteNf
paste True     = _
paste False    = joinC
paste (A ∨ B)  = joinC
paste (A ∧ B)  = < paste A ∘ mapC proj₁ , paste B ∘ mapC proj₂  >
paste (A ⇒ B) c τ a = paste B $ mapC' (λ δ f → f id≤ (monT A δ a)) $ monC (monT (A ⇒ B)) τ c

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

orElim : ∀ A B C {Γ} → T⟦ A ∨ B ⟧ Γ → T⟦ A ⇒ C ⟧ Γ → T⟦ B ⇒ C ⟧ Γ → T⟦ C ⟧ Γ
orElim A B C c g h = paste C (mapC' (λ τ → [ g τ , h τ ]) c)

-- A lemma for the falseE case.

-- Casts an empty cover into any semantic value (by contradiction).

falseElim : ∀ C → T⟦ False ⟧ →̇ T⟦ C ⟧
falseElim C = paste C ∘ mapC ⊥-elim

-- The fundamental theorem

eval :  ∀{A Γ} (t : Γ ⊢ A) → G⟦ Γ ⟧ →̇ T⟦ A ⟧
eval (hyp x)           = lookup x
eval (impI t)    γ τ a = eval t (monG τ γ , a)
eval (impE t u)  γ     = eval t γ id≤ (eval u γ)
eval (andI t u)  γ     = eval t γ , eval u γ
eval (andE₁ t)         = proj₁ ∘ eval t
eval (andE₂ t)         = proj₂ ∘ eval t
eval (orI₁ t)    γ     = returnC (inj₁ (eval t γ))
eval (orI₂ t)    γ     = returnC (inj₂ (eval t γ))
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

-- Q.E.D. -}
