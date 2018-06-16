

open import Library

module DanvyShiftReset where

postulate Base : Set

-- import Formulas   ; open module Form = Formulas    Base
-- import Derivations; open module Der  = Derivations Base
open import Formulas    Base
open import Derivations Base

Nf' : (C : Form) (Γ : Cxt) → Set
Nf' C Γ = Nf Γ C

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
  field run : KFun C B Γ → A Γ
open M

return : ∀{X A} → A →̇ M X X A
return x .run k = k id≤ x

_>>=_ : ∀{X Y Z A B Γ} (m : M X Y A Γ) (f : KFun A (M Y Z B) Γ) → M X Z B Γ
(m >>= f) .run k = m .run λ τ a → f τ a .run λ τ′ → k (τ′ • τ)

_<$>_ : ∀{X Y A B} (f : A →̇ B) → M X Y A →̇ M X Y B
(f <$> m) .run k = m .run λ τ → k τ ∘ f

liftA2 : ∀{X Y A B C} (f : ∀{Γ} → A Γ → B Γ → C Γ) → ∀{Γ} → M X Y A Γ → M X Y B Γ → M X Y C Γ
liftA2 f ma mb .run k = ma .run λ τ → {!mb .run!}

K$ : ∀{X Y A B} → KFun A B →̇ KFun (M X Y A) (M X Y B)
K$ f τ m .run k = m .run λ τ′ a →  k τ′ (f (τ′ • τ) a)

shift' : ∀{X Y A Γ} (f : KFun A Y Γ → X Γ) → M X Y A Γ
shift' f .run k = f k

shift : ∀{X Y A Γ} (f : KFun A Y Γ → M X Y Y Γ) → M X Y A Γ
shift f .run k = f k .run λ τ → id

reset' : ∀{Y A} → M A Y Y →̇ A
reset' m = m .run λ τ → id

reset : ∀{X Y A} → M A Y Y →̇ M X X A
reset m .run k = k id≤ (m .run λ τ → id)

T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
T⟦ Atom P ⟧ = Nf' (Atom P)
T⟦ True   ⟧ Γ = ⊤
T⟦ False  ⟧ Γ = ⊥
T⟦ A ∨ B  ⟧ Γ = T⟦ A ⟧ Γ ⊎ T⟦ B ⟧ Γ
T⟦ A ∧ B  ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
T⟦ A ⇒ B  ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ B ⟧ Δ

{-
-- Monotonicity of the model is proven by induction on the proposition,
-- using monotonicity of covers and the built-in monotonicity at implication.

-- monT : ∀ A {Γ Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ → T⟦ A ⟧ Δ

monT : ∀ A → Mon T⟦ A ⟧
monT (Atom P) = monNf
monT True     = _
monT False    = monCE λ τ ()
monT (A ∨ B)  = monCE λ τ → map-⊎ (monT A τ) (monT B τ)
monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
monT (A ⇒ B) τ f σ = f (σ • τ)
-}

-- Reflection / reification, proven simultaneously by induction on the proposition.

-- Reflection is η-expansion (and recursively reflection);
-- at positive connections we build a case tree with a single scrutinee: the neutral
-- we are reflecting.

-- At implication, we need reification, which produces introductions
-- and reifies the stored case trees.

mutual

  reflect : ∀{Γ} A (t : Ne Γ A) {C} → M (Nf' C) (Nf' C) T⟦ A ⟧ Γ
  reflect (Atom P) t = return (ne t)
  reflect True     t = return _
  reflect False    t = shift' λ k → falseE t
  reflect (A ∨ B)  t = shift' λ k → orE t
    (reset' (K$ k (weak id≤) (inj₁ <$> reflect A (hyp top))))
    ((inj₂ <$> reflect B (hyp top)) .run λ τ → k (τ • weak id≤))

    -- Wrong:
    --     (reset' (k (weak id≤) <$> (inj₁ <$> reflect A (hyp top))))

  -- reflect (A ∧ B) t = do
  --   a ← reflect A (andE₁ t)
  --   b ← reflect B (andE₂ t)
  --   return (a , b)

  -- reflect (A ∧ B) t = reflect A (andE₁ t) >>= λ τ a →
  --   reflect B (andE₂ t) >>= λ τ′ b →
  --   return (a , b)

{-
  reflect (A ⇒ B)  t τ a = reflect B (impE (monNe τ t) (reify A a))
-}

  reify : ∀{Γ} A (⟦f⟧ : T⟦ A ⟧ Γ) → Nf Γ A
  reify (Atom P) t      = t
  reify True _          = trueI
  reify False   ()
  reify (A ∨ B) (inj₁ a) = orI₁ (reify A a)
  reify (A ∨ B) (inj₂ b) = orI₂ (reify B b)
  reify (A ∧ B) (a , b) = andI (reify A a) (reify B b)
{-
  reify (A ⇒ B) ⟦f⟧     = impI (reify B (⟦f⟧ (weak id≤) (reflect A (hyp top))))
-}

{-
-- Semantic paste.

-- This grafts semantic values f onto a case tree C : Cover Γ.
-- For atomic propositions, this is grafting of normal forms (defined before).

paste : ∀ A {Γ} (C : Cover Γ) (f : All C (T⟦ A ⟧)) → T⟦ A ⟧ Γ
paste (Atom P) = paste'
paste True     = _
paste False    = transCE
paste (A ∨ B)  = transCE
paste (A ∧ B) C f = paste A C (proj₁ ∘ f) , paste B C (proj₂ ∘ f)
paste (A ⇒ B) C f τ a = paste B (monC τ C) λ {Δ} e → let Ψ , e' , σ  = mon∈ C τ e in f e' σ (monT A (coverWk e) a)

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

-- A lemma for the orE case.

orElim : ∀ {Γ A B X} → T⟦ A ∨ B ⟧ Γ →
         (∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ X ⟧ Δ) →
         (∀{Δ} (τ : Δ ≤ Γ) → T⟦ B ⟧ Δ → T⟦ X ⟧ Δ) →
         T⟦ X ⟧ Γ
orElim (C , f) g h = paste _ C λ e → [ g (coverWk e) , h (coverWk e) ] (f e)

-- A lemma for the falseE case.

-- Casts an empty cover into any semantic value (by contradiction).

falseElim : ∀{Γ A} → T⟦ False ⟧ Γ → T⟦ A ⟧ Γ
falseElim (C , f) = paste _ C (⊥-elim ∘ f)

-- The fundamental theorem

fund :  ∀{Γ A} (t : Γ ⊢ A) {Δ} (γ : G⟦ Γ ⟧ Δ) → T⟦ A ⟧ Δ
fund (hyp x)           = fundH x
fund (impI t)    γ τ a = fund t (monG τ γ , a)
fund (impE t u)  γ     = fund t γ id≤ (fund u γ)
fund (andI t u)  γ     = fund t γ , fund u γ
fund (andE₁ t)         = proj₁ ∘ fund t
fund (andE₂ t)         = proj₂ ∘ fund t
fund (orI₁ t)    γ     = hole , inj₁ ∘ λ{ here → fund t γ }
fund (orI₂ t)    γ     = hole , inj₂ ∘ λ{ here → fund t γ }
fund (orE t u v) γ     = orElim (fund t γ)
  (λ τ a → fund u (monG τ γ , a))
  (λ τ b → fund v (monG τ γ , b))
fund (falseE t)  γ     = falseElim (fund t γ)
fund trueI       γ     = _

-- Identity environment

ide : ∀ Γ → G⟦ Γ ⟧ Γ
ide ε = _
ide (Γ ∙ A) = monG (weak id≤) (ide Γ) , reflect A (hyp top)

-- Normalization

norm : ∀{Γ A} (t : Γ ⊢ A) → Nf Γ A
norm t = reify _ (fund t (ide _))

-- Q.E.D. -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
