-- An implementation of Olivier Danvy's Type-Directed Partial Evaluation (POPL 1996)
-- for STLC with sum types using continuations in form of shift and reset.
--
-- The algorithm was originally for a two-level lambda-calculus.

-- Our use of Kripke semantics makes the effect of fresh variable generation explicit and formal.

open import Library

module DanvyShiftResetLiftable where

data Base : Set where
  α β : Base

open import Formulas    Base
open import Derivations Base

-- Continutation monad with answer type R.
-- (Cf. Haskell's Control.Monad.Cont.Cont = (A → R) → R).

record M (R A : Cxt → Set) (Γ : Cxt) : Set where
  constructor shift
  field run : KFun (KFun A R) R Γ
open M

-- shift : ∀{R A Γ} (f : KFun (KFun A R) R Γ) → M R A Γ
-- shift f .run σ k = f σ k

reset : ∀{A} → M A A →̇ A
reset m = m .run id≤ λ τ → id

return : ∀{R A} → □ A →̇ M R A
return x .run τ k = k id≤ (x τ)

return' : ∀{R A} → □ A →̇ M R (□ A)
return' x .run τ k = k id≤ λ τ₁ → x (τ₁ • τ)

-- Bind

_>>=_ : ∀{R A B Γ} (m : M R A Γ) (f : KFun A (M R B) Γ) → M R B Γ
(m >>= f) .run σ k = m .run σ λ τ a → f (τ • σ) a .run id≤ λ τ′ → k (τ′ • τ)

-- Map

_<$>_ : ∀{R A B} (f : A →̇ B) → M R A →̇ M R B
(f <$> m) .run σ k = m .run σ λ τ → k τ ∘ f

_<&>_ : ∀{R A B Γ} (m : M R A Γ) (f : A →̇ B) → M R B Γ
(m <&> f) .run σ k = m .run σ λ τ → k τ ∘ f

-- Kripke map

K$ : ∀{R A B} → KFun A B →̇ KFun (M R A) (M R B)
K$ f τ m .run σ k = m .run σ λ τ′ a →  k τ′ (f (τ′ • (σ • τ)) a)

-- We use a continuation monad with answer type Nf.

Ne' : (C : Form) (Γ : Cxt) → Set
Ne' C Γ = Ne Γ C

Nf' : (C : Form) (Γ : Cxt) → Set
Nf' C Γ = Nf Γ C

M' : (X : Cxt → Set) (Γ : Cxt) → Set
M' X Γ = ∀ {C} → M (Nf' C) X Γ

T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
T⟦ Atom P ⟧ = □ (Nf' (Atom P))
T⟦ True   ⟧ Γ = ⊤
T⟦ False  ⟧ Γ = ⊥
T⟦ A ∨ B  ⟧ Γ = T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ
T⟦ A ∧ B  ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
T⟦ A ⇒ B  ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → M' T⟦ B ⟧ Δ

-- Monotonicity of the model is proven by induction on the proposition.

-- monT : ∀ A {Γ Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ → T⟦ A ⟧ Δ

monT : ∀ A → Mon T⟦ A ⟧
monT (Atom P) = mon□
monT True     = _
monT False  τ ()
monT (A ∨ B) τ = map-⊎ (monT A τ) (monT B τ)
monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
monT (A ⇒ B) τ f σ = f (σ • τ)

fresh : ∀{A Γ} → □ (Ne' A) (Γ ∙ A)
fresh τ′ = hyp (monH τ′ top)

-- Reflection / reification, proven simultaneously by induction on the proposition.

-- Reflection is η-expansion (and recursively reflection);

mutual

  reflect : ∀ A → □ (Ne' A) →̇ M' T⟦ A ⟧
  reflect (Atom P) t = return' (ne ∘′ t) -- λ τ → ne (monNe τ t)
  reflect True     t = return _
  reflect False    t = shift λ τ k → falseE (t τ)
  reflect (A ∨ B)  t = shift λ τ k → orE (t τ)
    (reset (K$ k (weak id≤) (inj₁ <$> reflect A fresh)))
    (reset (K$ k (weak id≤) (inj₂ <$> reflect B fresh)))

    -- ((inj₂ <$> reflect B (hyp top)) .run λ τ → k (τ • weak id≤))
    -- Wrong:
    --     (reset (k (weak id≤) <$> (inj₁ <$> reflect A (hyp top))))

  -- reflect (A ∧ B) t = do
  --   a ← reflect A (andE₁ t)
  --   b ← reflect B (andE₂ t)
  --   return (a , b)

  reflect (A ∧ B) t =
    reflect A (                andE₁ ∘ t ) >>= λ τ a →
    reflect B (mon□ {Ne' B} τ (andE₂ ∘ t)) >>= λ τ′ b →
    return λ τ₁ → monT A (τ₁ • τ′) a , monT B τ₁ b

  reflect (A ⇒ B)  t = return' λ τ a → reflect B λ τ′ → impE (t (τ′ • τ)) (reify A a τ′)


  reify : ∀ A → T⟦ A ⟧ →̇ □ (Nf' A)

  reify (Atom P) t = t
  reify True     _       τ = trueI
  reify False   ()
  reify (A ∨ B) (inj₁ a) τ = orI₁ (reify A a τ)
  reify (A ∨ B) (inj₂ b) τ = orI₂ (reify B b τ)
  reify (A ∧ B) (a , b) τ = andI (reify A a τ) (reify B b τ)

  reify (A ⇒ B) f       τ = impI $ reset $
    reflect A fresh >>= λ τ′ a →
    f (τ′ • weak τ) a <&> λ b →
    reify B b id≤


-- Fundamental theorem

-- Delayed lifting

record ◇ (G : Cxt → Set) (Γ : Cxt) : Set where
  constructor dia; field
    {Δ} : Cxt
    τ   : Γ ≤ Δ
    γ   : G Δ

mon◇ : ∀{P} → Mon (◇ P)
mon◇ τ′ (dia τ x) = dia (τ′ • τ) x

-- Extension of T⟦_⟧ to contexts to classify semantic environments.

G⟦_⟧ : ∀ (Γ Δ : Cxt) → Set
G⟦ ε     ⟧ _ = ⊤
G⟦ Γ ∙ A ⟧ = ◇ λ Δ → G⟦ Γ ⟧ Δ × T⟦ A ⟧ Δ

-- monG is lazy except for matching on the context.

monG : ∀{Γ} → Mon G⟦ Γ ⟧
monG {ε} τ _ = _
monG {Γ ∙ A} τ γ = mon◇ τ γ

-- Environment extension.

ext : ∀ A {Γ Δ₁ Δ} →
      (τ : Δ ≤ Δ₁) (γ : G⟦ Γ ⟧ Δ₁) →
      (a : T⟦ A ⟧ Δ) →
      □ G⟦ Γ ∙ A ⟧ Δ
ext A τ γ a τ′ = dia τ′ (monG τ γ , a)

-- Lookup in the environment.
-- Accumulates embedded weakenings from environment.

fundH : ∀{A Γ} (x : Hyp A Γ) → G⟦ Γ ⟧  →̇ □ T⟦ A ⟧
fundH {A} top (dia τ′ (_ , a)) τ = monT A (τ • τ′) a
fundH (pop x) (dia τ′ (γ , _)) τ = fundH x γ (τ • τ′)

-- The fundamental theorem:
-- A call-by-value interpreter.

fund :  ∀{Γ A} (t : Γ ⊢ A) → G⟦ Γ ⟧  →̇ M' T⟦ A ⟧

fund (hyp {A} x) γ = return (fundH x γ)
fund (impI {A} t) γ = return' λ τ a → fund t (ext A τ γ a id≤)

fund (impE t u)  γ =
  fund t γ          >>= λ τ f →
  fund u (monG τ γ) >>= λ τ′ a →
  f τ′ a

fund (andI {A} {B} t u) γ =
  fund t γ          >>= λ τ a →
  fund u (monG τ γ) >>= λ τ′ b →
  return λ τ₁ → monT A (τ₁ • τ′) a , monT B τ₁ b

fund (andE₁ t)    γ = proj₁ <$> fund t γ
fund (andE₂ t)    γ = proj₂ <$> fund t γ
fund (orI₁ t)     γ = inj₁  <$> fund t γ
fund (orI₂ t)     γ = inj₂  <$> fund t γ

fund (orE {A} {B} t u v) γ = fund t γ >>= λ τ →
  [ (λ a → fund u (ext A τ γ a id≤))
  , (λ b → fund v (ext B τ γ b id≤))
  ]

fund (falseE t)  γ = fund t γ >>= λ τ ()
fund trueI       γ = return _

-- Identity environment

ide : ∀ Γ → □ (M' G⟦ Γ ⟧) Γ
ide ε       τ = return _
ide (Γ ∙ A) τ =
  ide Γ (τ • weak id≤)           >>= λ τ₁ γ →
  reflect A (mon□ (τ₁ • τ) fresh) >>= λ τ₂ a →
  return (ext A τ₂ γ a)
  -- return λ τ₃ → dia τ₃ (monG τ₂ γ , a)

-- Normalization

norm : ∀{A Γ} (t : Γ ⊢ A) → Nf Γ A
norm {A} {Γ} t = reset $
  ide Γ id≤ >>= λ _ γ →
  fund t γ <&> λ a →
  reify A a id≤

-- Testing

idD : (A : Form) → ε ⊢ (A ⇒ A)
idD A = impI (hyp top)

test : let A = Atom α; B = Atom β in Nf ε (A ∨ B ⇒ A ∨ B)
test = norm (idD (Atom α ∨ Atom β))

test2 = norm (idD (Atom α ∨ Atom β ∨ Atom α))

test3 = norm (idD False)

-- Q.E.D. -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
