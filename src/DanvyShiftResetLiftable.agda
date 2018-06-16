

open import Library

module DanvyShiftResetLiftable where

data Base : Set where
  α β : Base

open import Formulas    Base
open import Derivations Base

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

_<&>_ : ∀{X Y A B Γ} (m : M X Y A Γ) (f : A →̇ B) → M X Y B Γ
(m <&> f) .run σ k = m .run σ λ τ → k τ ∘ f

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

Ne' : (C : Form) (Γ : Cxt) → Set
Ne' C Γ = Ne Γ C

Nf' : (C : Form) (Γ : Cxt) → Set
Nf' C Γ = Nf Γ C

M' : (X : Cxt → Set) (Γ : Cxt)→ Set
M' X Γ = ∀ {C} → M (Nf' C) (Nf' C) X Γ

T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
T⟦ Atom P ⟧ = □ (Nf' (Atom P))
T⟦ True   ⟧ Γ = ⊤
T⟦ False  ⟧ Γ = ⊥
T⟦ A ∨ B  ⟧ Γ = T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ
T⟦ A ∧ B  ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
T⟦ A ⇒ B  ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → M' T⟦ B ⟧ Δ

-- Monotonicity of the model is proven by induction on the proposition,
-- using monotonicity of covers and the built-in monotonicity at implication.

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
  reflect False    t = shift' λ τ k → falseE (t τ)
  reflect (A ∨ B)  t = shift' λ τ k → orE (t τ)
    (reset' (K$ k (weak id≤) (inj₁ <$> reflect A fresh)))
    (reset' (K$ k (weak id≤) (inj₂ <$> reflect B fresh)))

    -- ((inj₂ <$> reflect B (hyp top)) .run λ τ → k (τ • weak id≤))
    -- Wrong:
    --     (reset' (k (weak id≤) <$> (inj₁ <$> reflect A (hyp top))))

  -- reflect (A ∧ B) t = do
  --   a ← reflect A (andE₁ t)
  --   b ← reflect B (andE₂ t)
  --   return (a , b)

  reflect (A ∧ B) t =
    reflect A (                andE₁ ∘ t ) >>= λ τ a →
    reflect B (mon□ {Ne' B} τ (andE₂ ∘ t)) >>= λ τ′ b →
    return λ τ₁ → monT A (τ₁ • τ′) a , monT B τ₁ b

  reflect (A ⇒ B)  t = return' λ τ a → reflect B (λ τ′ → impE (t (τ′ • τ)) (reify A a τ′))


  reify : ∀ A → T⟦ A ⟧ →̇ □ (Nf' A)

  reify (Atom P) t = t
  reify True     _       τ = trueI
  reify False   ()
  reify (A ∨ B) (inj₁ a) τ = orI₁ (reify A a τ)
  reify (A ∨ B) (inj₂ b) τ = orI₂ (reify B b τ)
  reify (A ∧ B) (a , b) τ = andI (reify A a τ) (reify B b τ)

  reify (A ⇒ B) f       τ = impI $ reset' $
    reflect A fresh >>= λ τ′ a →
    f (τ′ • weak τ) a <&> λ b →
    reify B b id≤


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
  ide Γ (τ • weak id≤)           >>= λ τ₁ γ →
  reflect A (mon□ (τ₁ • τ) fresh) >>= λ τ₂ a →
  return λ τ₃ → monG (τ₃ • τ₂) γ , monT A τ₃ a

-- Normalization

norm : ∀{A Γ} (t : Γ ⊢ A) → Nf Γ A
norm {A} {Γ} t = reset' $
  ide Γ id≤ >>= λ _ γ →
  fund t γ <&> λ a →
  reify A a id≤

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
