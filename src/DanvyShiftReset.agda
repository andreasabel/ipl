-- An implementation of Olivier Danvy's Type-Directed Partial Evaluation (POPL 1996)
-- for STLC with sum types using continuations in form of shift and reset.
--
-- The algorithm was originally for a two-level lambda-calculus.

-- Our use of Kripke semantics makes the effect of fresh variable generation explicit and formal.


open import Library

module DanvyShiftReset where

data Base : Set where
  α β : Base

-- import Formulas   ; open module Form = Formulas    Base
-- import Derivations; open module Der  = Derivations Base
open import Formulas    Base
open import Derivations Base

-- -- Shift-reset continutation monad

-- record M (A B C : Set) : Set where
--   field run : (C → B) → A
-- open M

-- return : ∀{X A} → A → M X X A
-- return x .run k = k x

-- _>>=_ : ∀{X Y Z A B} (m : M X Y A) (f : A → M Y Z B) → M X Z B
-- (m >>= f) .run k = m .run λ a → f a .run k

-- _<$>_ : ∀{X Y A B} (f : A → B) (m : M X Y A) → M X Y B
-- (f <$> m) .run k = m .run (k ∘ f)

-- shift : ∀{X Y A} (f : (A → Y) → M X Y Y) → M X Y A
-- shift f .run k = f k .run id

-- shift' : ∀{X Y A} (f : (A → Y) → X) → M X Y A
-- shift' f .run k = f k

-- reset : ∀{X Y A} (m : M A Y Y) → M X X A
-- reset m .run k = k (m .run id)

-- Shift-reset continutation monad

record M (A B C : Cxt → Set) (Γ : Cxt) : Set where
  field run : KFun (KFun C B) A Γ
open M

return : ∀{X A} → □ A →̇ M X X A
return x .run τ k = k id≤ (x τ)

return' : ∀{X A} → □ A →̇ M X X (□ A)
return' x .run τ k = k id≤ λ τ₁ → x (τ₁ • τ)

_>>=_ : ∀{X Y Z A B Γ} (m : M X Y A Γ) (f : KFun A (M Y Z B) Γ) → M X Z B Γ
(m >>= f) .run σ k = m .run σ λ τ a → f (τ • σ) a .run id≤ λ τ′ → k (τ′ • τ)

_<$>_ : ∀{X Y A B} (f : A →̇ B) → M X Y A →̇ M X Y B
(f <$> m) .run σ k = m .run σ λ τ → k τ ∘ f

-- liftA2 : ∀{X Y A B C} (f : ∀{Γ} → A Γ → B Γ → C Γ) → ∀{Γ} → M X Y A Γ → M X Y B Γ → M X Y C Γ
-- liftA2 f ma mb .run σ k = ma .run σ λ τ a → {!mb .run!}

K$ : ∀{X Y A B} → KFun A B →̇ KFun (M X Y A) (M X Y B)
K$ f τ m .run σ k = m .run σ λ τ′ a →  k τ′ (f (τ′ • (σ • τ)) a)

shift' : ∀{X Y A Γ} (f : KFun (KFun A Y) X Γ) → M X Y A Γ
shift' f .run σ k = f σ k

shift : ∀{X Y A Γ} (f : KFun (KFun A Y) (M X Y Y) Γ) → M X Y A Γ
shift f .run σ k = f σ k .run id≤ λ τ → id

reset' : ∀{Y A} → M A Y Y →̇ A
reset' m = m .run id≤ λ τ → id

reset : ∀{X Y A} → M A Y Y →̇ M X X A
reset m .run σ k = k id≤ (m .run σ λ τ → id)

-- We use a continuation monad with answer type Nf.

M' : (X : Cxt → Set) (Γ : Cxt) → Set
M' X Γ = ∀ {C} → M (Nf' C) (Nf' C) X Γ

T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
T⟦ Atom P ⟧ = Nf' (Atom P)
T⟦ True   ⟧ Γ = ⊤
T⟦ False  ⟧ Γ = ⊥
T⟦ A ∨ B  ⟧ Γ = T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ
T⟦ A ∧ B  ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
T⟦ A ⇒ B  ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → M' T⟦ B ⟧ Δ

-- Monotonicity of the model is proven by induction on the proposition.

-- monT : ∀ A {Γ Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ → T⟦ A ⟧ Δ

monT : ∀ A → Mon T⟦ A ⟧
monT (Atom P) = monNf
monT True     = _
monT False  τ ()
monT (A ∨ B) τ = map-⊎ (monT A τ) (monT B τ)
monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
monT (A ⇒ B) τ f σ = f (σ • τ)


-- Reflection / reification, proven simultaneously by induction on the proposition.

-- Reflection is η-expansion (and recursively reflection);

mutual

  reflect : ∀{Γ} A (t : Ne Γ A) → M' T⟦ A ⟧ Γ
  reflect (Atom P) t = return λ τ → ne (monNe τ t)
  reflect True     t = return _
  reflect False    t = shift' λ τ k → falseE (monNe τ t)
  reflect (A ∨ B)  t = shift' λ τ k → orE (monNe τ t)
    (reset' (K$ k (weak id≤) (inj₁ <$> reflect A (hyp top))))
    (reset' (K$ k (weak id≤) (inj₂ <$> reflect B (hyp top))))

    -- ((inj₂ <$> reflect B (hyp top)) .run λ τ → k (τ • weak id≤))
    -- Wrong:
    --     (reset' (k (weak id≤) <$> (inj₁ <$> reflect A (hyp top))))

  -- reflect (A ∧ B) t = do
  --   a ← reflect A (andE₁ t)
  --   b ← reflect B (andE₂ t)
  --   return (a , b)

  reflect (A ∧ B) t =
    reflect A (andE₁ t          ) >>= λ τ a →
    reflect B (andE₂ (monNe τ t)) >>= λ τ′ b →
    return λ τ₁ → monT A (τ₁ • τ′) a , monT B τ₁ b

  reflect (A ⇒ B)  t = return' λ τ a → reflect B (impE (monNe τ t) (reify A a))


  reify : ∀{Γ} A (⟦f⟧ : T⟦ A ⟧ Γ) → Nf Γ A

  reify (Atom P) t      = t
  reify True _          = trueI
  reify False   ()
  reify (A ∨ B) (inj₁ a) = orI₁ (reify A a)
  reify (A ∨ B) (inj₂ b) = orI₂ (reify B b)
  reify (A ∧ B) (a , b) = andI (reify A a) (reify B b)

  reify (A ⇒ B) f     = impI $ reset' $
    reflect A (hyp top) >>= λ τ a →
    reify B <$> f (τ • weak id≤) a


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

fundH : ∀{Γ Δ A} (x : Hyp A Γ) (γ : G⟦ Γ ⟧ Δ) → T⟦ A ⟧ Δ
fundH top     = proj₂
fundH (pop x) = fundH x ∘ proj₁

-- The fundamental theorem:
-- A call-by-value interpreter.

fund :  ∀{Γ A} (t : Γ ⊢ A) {Δ} (γ : G⟦ Γ ⟧ Δ) → M' T⟦ A ⟧ Δ

fund (hyp {A} x) γ = return λ τ → monT A τ (fundH x γ)
fund (impI t)    γ = return' λ τ a → fund t (monG τ γ , a)

fund (impE t u)  γ =
  fund t γ          >>= λ τ f →
  fund u (monG τ γ) >>= λ τ′ a →
  f τ′ a

fund (andI {A} {B} t u) γ =
  fund t γ >>= λ τ a →
  fund u (monG τ γ) >>= λ τ′ b →
  return λ τ₁ → monT A (τ₁ • τ′) a , monT B τ₁ b

fund (andE₁ t)    γ = proj₁ <$> fund t γ
fund (andE₂ t)    γ = proj₂ <$> fund t γ
fund (orI₁ t)     γ = inj₁  <$> fund t γ
fund (orI₂ t)     γ = inj₂  <$> fund t γ

fund (orE t u v) γ = fund t γ >>= λ τ →
  [ (λ a → fund u (monG τ γ , a))
  , (λ b → fund v (monG τ γ , b))
  ]

fund (falseE t)  γ = fund t γ >>= λ τ ()
fund trueI       γ = return _

-- Identity environment

ide : ∀ Γ → □ (M' G⟦ Γ ⟧) Γ
ide ε       τ = return _
ide (Γ ∙ A) τ =
  ide Γ (τ • weak id≤)                >>= λ τ₁ γ →
  reflect A (monNe (τ₁ • τ) (hyp top)) >>= λ τ₂ a →
  return λ τ₃ → monG (τ₃ • τ₂) γ , monT A τ₃ a

-- Normalization

norm : ∀{A Γ} (t : Γ ⊢ A) → Nf Γ A
norm {A} {Γ} t = reset' $
  ide Γ id≤ >>= λ _ γ →
  reify A <$> fund t γ

idD : (A : Form) → ε ⊢ (A ⇒ A)
idD A = impI (hyp top)

test : let A = Atom α; B = Atom β in Nf ε (A ∨ B ⇒ A ∨ B)
test = norm (idD (Atom α ∨ Atom β))

test2 = norm (idD (Atom α ∨ Atom β ∨ Atom α))

-- Q.E.D. -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
