{-# OPTIONS --rewriting #-}

module NfCBPV where

open import Library hiding (_×̇_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

postulate Base : Set

set = ℕ
El  = Fin

variable
  I : set
  i : El I

mutual

  -- Value types

  data Ty⁺ : Set where
    base    : (o : Base) → Ty⁺
    _×̇_     : (P₁ P₂ : Ty⁺) → Ty⁺
    Σ̇       : (I : set) (Ps : El I → Ty⁺) → Ty⁺
    □̇       : (N : Ty⁻) → Ty⁺      -- U

  -- Computation types

  data Ty⁻ : Set where
    ◇̇   : (P : Ty⁺) → Ty⁻     -- F
    Π̇      : (I : set) (Ns : El I → Ty⁻) → Ty⁻
    _⇒̇_    : (P : Ty⁺) (N : Ty⁻) → Ty⁻

-- Environments only contain values

Cxt = List Ty⁺

variable
  Γ Δ Φ : Cxt
  P P₁ P₂ P' P′ Q : Ty⁺
  N N₁ N₂ N' N′ : Ty⁻
  Ps : El I → Ty⁺
  Ns : El I → Ty⁻

pattern here! = here refl
-- pattern suc  = there

-- Generic values

module _ (Var : Ty⁺ → Cxt → Set) (Comp : Ty⁻ → Cxt → Set) where

  -- Right non-invertible

  data Val' : (P : Ty⁺) (Γ : Cxt) → Set where
    var   : ∀{Γ P}     (x : Var P Γ)                     → Val' P Γ
    pair  : ∀{Γ P₁ P₂} (v₁ : Val' P₁ Γ) (v₂ : Val' P₂ Γ) → Val' (P₁ ×̇ P₂) Γ
    inj   : ∀{Γ I P} i (v : Val' (P i) Γ)                → Val' (Σ̇ I P) Γ
    thunk : ∀{Γ N}     (t : Comp N Γ)                    → Val' (□̇ N) Γ

-- Terms

mutual

  Val = Val' _∈_ Comp

  data Comp : (N : Ty⁻) (Γ : Cxt) → Set where
    -- introductions
    ret   : ∀{Γ P}       (v : Val P Γ)                → Comp (◇̇ P) Γ
    rec   : ∀{Γ I N}     (t : ∀ i → Comp (N i) Γ)     → Comp (Π̇ I N) Γ
    abs   : ∀{Γ P N}     (t : Comp N (P ∷ Γ))         → Comp (P ⇒̇ N) Γ
    -- positive eliminations
    split : ∀{Γ P₁ P₂ N} (v : Val (P₁ ×̇ P₂) Γ) (t : Comp N (P₂ ∷ P₁ ∷ Γ)) → Comp N Γ
    case  : ∀{Γ I Ps N}  (v : Val (Σ̇ I Ps) Γ) (t : ∀ i → Comp N (Ps i ∷ Γ)) → Comp N Γ
    bind  : ∀{Γ P N}     (u : Comp (◇̇ P) Γ) (t : Comp N (P ∷ Γ)) → Comp N Γ
    -- negative elimination
    force : ∀{Γ N}       (v : Val (□̇ N) Γ)   → Comp N Γ
    prj   : ∀{Γ I Ns} i  (t : Comp (Π̇ I Ns) Γ)                       → Comp (Ns i) Γ
    app   : ∀{Γ P N}     (t : Comp (P ⇒̇ N) Γ)   (v : Val P Γ)        → Comp N Γ
    -- cut
    letv  : ∀{Γ P N}     (v : Val P Γ)         (t : Comp N (P ∷ Γ)) → Comp N Γ

-- Normal forms
------------------------------------------------------------------------

-- Normal values only reference variables of base type

NVar : (P : Ty⁺) (Γ : Cxt) → Set
NVar (base o) Γ = base o ∈ Γ
NVar _ _ = ⊥

-- Negative neutrals

module _ (Val : Ty⁺ → Cxt → Set) where

  -- Right non-invertible

  data Ne' : (N : Ty⁻) (Γ : Cxt) → Set where
    force : ∀{Γ N}     (x : □̇ N ∈ Γ)                     → Ne' N Γ
    prj   : ∀{Γ I N} i (t : Ne' (Π̇ I N) Γ)               → Ne' (N i) Γ
    app   : ∀{Γ P N}   (t : Ne' (P ⇒̇ N) Γ) (v : Val P Γ) → Ne' N Γ

mutual

  NVal = Val' NVar Nf
  Ne   = Ne' NVal

  -- Cover monad

  data ◇ (J : Cxt → Set) (Γ : Cxt) : Set where
    return : (j : J Γ)                                               → ◇ J Γ
    bind   : ∀{P}     (u : Ne (◇̇ P) Γ)    (t :          ◇ J (P ∷ Γ)) → ◇ J Γ
    case   : ∀{I Ps}  (x : Σ̇ I Ps ∈ Γ)    (t : ∀ i → ◇ J (Ps i ∷ Γ)) → ◇ J Γ
    split  : ∀{P₁ P₂} (x : (P₁ ×̇ P₂) ∈ Γ) (t :    ◇ J (P₂ ∷ P₁ ∷ Γ)) → ◇ J Γ

  data NComp (Q : Ty⁺) (Γ : Cxt) : Set where
    ret   :          (v : NVal Q Γ)   → NComp Q Γ   -- Invoke RFoc
    ne    :          (n : Ne (◇̇ Q) Γ) → NComp Q Γ   -- Finish with LFoc
      -- e.g. app (force f) x

    -- Use lemma LFoc
    bind  : ∀{P}     (u : Ne (◇̇ P) Γ) (t : NComp Q (P ∷ Γ)) → NComp Q Γ

    -- Left invertible
    split : ∀{P₁ P₂} (x : (P₁ ×̇ P₂) ∈ Γ) (t :    NComp Q (P₂ ∷ P₁ ∷ Γ)) → NComp Q Γ
    case  : ∀{I Ps}  (x : Σ̇ I Ps    ∈ Γ) (t : ∀ i → NComp Q (Ps i ∷ Γ)) → NComp Q Γ

  -- Right invertible

  data Nf : (N : Ty⁻) (Γ : Cxt) → Set where
    ret   : ∀{Γ P}   (v : ◇ (NVal P) Γ)     → Nf (◇̇ P) Γ   -- Invoke RFoc
    ne    : ∀{Γ o}   (let N = ◇̇ (base o))
                     (n : ◇ (Ne N) Γ)       → Nf N Γ
    -- comp  : ∀{Γ P}   (t : NComp P Γ)        → Nf (◇̇ P) Γ
    rec   : ∀{Γ I N} (t : ∀ i → Nf (N i) Γ) → Nf (Π̇ I N) Γ
    abs   : ∀{Γ P N} (t : Nf N (P ∷ Γ))     → Nf (P ⇒̇ N) Γ

-- Context-indexed sets
------------------------------------------------------------------------

ISet = (Γ : Cxt) → Set

variable
  A B C : ISet
  F G   : (i : El I) → ISet

-- Constructions on ISet

1̂ : ISet
1̂ Γ = ⊤

_×̂_ : (A B : ISet) → ISet
(A ×̂ B) Γ = A Γ × B Γ

Σ̂ : (I : set) (F : El I → ISet) → ISet
(Σ̂ I F) Γ = ∃ λ i → F i Γ

_⇒̂_ : (A B : ISet) → ISet
(A ⇒̂ B) Γ = A Γ → B Γ

Π̂ : (I : set) (F : El I → ISet) → ISet
(Π̂ I F) Γ = ∀ i → F i Γ

⟨_⟩ : (P : Ty⁺) (A : ISet) → ISet
⟨ P ⟩ A Γ = A (P ∷ Γ)

-- Morphisms between ISets

_→̇_ : (A B : Cxt → Set) → Set
A →̇ B = ∀{Γ} → A Γ → B Γ

⟨_⊙_⟩→̇_ : (P Q R : Cxt → Set) → Set
⟨ P ⊙ Q ⟩→̇ R = ∀{Γ} → P Γ → Q Γ → R Γ

⟨_⊙_⊙_⟩→̇_ : (P Q R S : Cxt → Set) → Set
⟨ P ⊙ Q ⊙ R ⟩→̇ S = ∀{Γ} → P Γ → Q Γ → R Γ → S Γ

Map : (F : (Cxt → Set) → Cxt → Set) → Set₁
Map F = ∀{A B : Cxt → Set} (f : A →̇ B) → F A →̇ F B

Π-map : (∀ i → F i →̇ G i) → Π̂ I F →̇ Π̂ I G
Π-map f r i = f i (r i)

-- -- Introductions and eliminations for ×̂

-- p̂air : ⟨ A ⊙ B ⟩→̇ (A ×̂ B)
-- p̂air a b = λ

-- Monotonicity
------------------------------------------------------------------------

-- Monotonization □ is a monoidal comonad

□ : (A : Cxt → Set) → Cxt → Set
□ A Γ = ∀{Δ} (τ : Γ ⊆ Δ) → A Δ

extract : □ A →̇ A
extract a = a ⊆-refl

duplicate : □ A →̇ □ (□ A)
duplicate a τ τ′ = a (⊆-trans τ τ′)

□-map : Map □
□-map f a τ = f (a τ)

extend : (□ A →̇ B) → □ A →̇ □ B
extend f = □-map f ∘ duplicate

□-weak : □ A →̇ ⟨ P ⟩ (□ A)
□-weak a τ = a (⊆-trans (_ ∷ʳ ⊆-refl) τ)

□-weak' : □ A →̇ □ (⟨ P ⟩ A)
□-weak' a τ = a (_ ∷ʳ τ)

□-sum : Σ̂ I (□ ∘ F) →̇ □ (Σ̂ I F)
□-sum (i , a) τ = i , a τ

-- Monoidality:

□-unit : 1̂ →̇ □ 1̂
□-unit = _

□-pair : ⟨ □ A ⊙ □ B ⟩→̇ □ (A ×̂ B)
□-pair a b τ = (a τ , b τ)

-- Strong functoriality

Map! : (F : (Cxt → Set) → Cxt → Set) → Set₁
Map! F = ∀{A B : Cxt → Set} → ⟨ □ (A ⇒̂ B) ⊙ F A ⟩→̇ F B

-- Monotonicity

Mon : (A : Cxt → Set) → Set
Mon A = A →̇ □ A

monVar : Mon (P ∈_)
monVar x τ = ⊆-lookup τ x

-- Positive ISets are monotone

□-mon : Mon (□ A)
□-mon = duplicate

1-mon : Mon 1̂
1-mon = □-unit

×-mon : Mon A → Mon B → Mon (A ×̂ B)
×-mon mA mB (a , b) = □-pair (mA a) (mB b)

Σ-mon : ((i : El I) → Mon (F i)) → Mon (Σ̂ I F)
Σ-mon m (i , a) = □-sum (i , m i a)

□-intro : Mon A → (A →̇ B) → (A →̇ □ B)
□-intro mA f = □-map f ∘ mA

-- Cover monad: a strong monad
------------------------------------------------------------------------

join : ◇ (◇ A) →̇ ◇ A
join (return c)  = c
join (bind u c)  = bind u (join c)
join (case x t)  = case x (join ∘ t)
join (split x c) = split x (join c)

◇-map : Map ◇
◇-map f (return  j) = return  (f j)
◇-map f (bind  u a) = bind  u (◇-map f a)
◇-map f (case  x t) = case  x (λ i → ◇-map f (t i))
◇-map f (split x a) = split x (◇-map f a)

◇-map! : Map! ◇
◇-map! f (return  j) = return  (extract f j)
◇-map! f (bind  u a) = bind  u (◇-map! (□-weak f) a)
◇-map! f (case  x t) = case  x (λ i → ◇-map! (□-weak f) (t i))
◇-map! f (split x a) = split x (◇-map! (□-weak (□-weak f)) a)

◇-bind : A →̇ ◇ B → ◇ A →̇ ◇ B
◇-bind f = join ∘ ◇-map f

◇-record : ◇ (Π̂ I F) →̇ Π̂ I (◇ ∘ F)
◇-record c i = ◇-map (_$ i) c

◇-fun : Mon A → ◇ (A ⇒̂ B) →̇ (A ⇒̂ ◇ B)
◇-fun mA c a = ◇-map! (λ τ f → f (mA a τ)) c

-- Monoidal functoriality

-- ◇-pair : ⟨ ◇ A ⊙ ◇ B ⟩→̇ ◇ (A ×̂ B)  -- does not hold!

◇-pair : ⟨ □ (◇ A) ⊙ ◇ (□ B) ⟩→̇ ◇ (A ×̂ B)
◇-pair ca = join ∘ ◇-map! λ τ b → ◇-map! (λ τ′ a → a , b τ′) (ca τ)

_⋉_ = ◇-pair

□◇-pair' : ⟨ □ (◇ A) ⊙ □ (◇ (□ B)) ⟩→̇ □ (◇ (A ×̂ B))
□◇-pair' ca cb τ = ◇-pair (□-mon ca τ) (cb τ)

□◇-pair : Mon B → ⟨ □ (◇ A) ⊙ □ (◇ B) ⟩→̇ □ (◇ (A ×̂ B))
□◇-pair mB ca cb τ = join $
  ◇-map! (λ τ₁ b → ◇-map! (λ τ₂ a → a , mB b τ₂) (ca (⊆-trans τ τ₁))) (cb τ)

◇□-pair' : ⟨ ◇ (□ A) ⊙ □ (◇ (□ B)) ⟩→̇ ◇ (□ (A ×̂ B))
◇□-pair' ca cb = join (◇-map! (λ τ a → ◇-map! (λ τ₁ b τ₂ → a (⊆-trans τ₁ τ₂) , b τ₂) (cb τ)) ca)

◇□-pair : ⟨ □ (◇ (□ A)) ⊙ ◇ (□ B) ⟩→̇ ◇ (□ (A ×̂ B))
◇□-pair ca cb = join (◇-map! (λ τ b → ◇-map! (λ τ₁ a τ₂ → a τ₂ , b (⊆-trans τ₁ τ₂)) (ca τ)) cb)

-- Runnability

Run : (A : Cxt → Set) → Set
Run A = ◇ A →̇ A

-- Negative ISets are runnable

◇-run : Run (◇ A)
◇-run = join

Π-run : (∀ i → Run (F i)) → Run (Π̂ I F)
Π-run f = Π-map f ∘ ◇-record

⇒-run : Mon A → Run B → Run (A ⇒̂ B)
⇒-run mA rB f = rB ∘ ◇-fun mA f

-- Bind for the ◇ monad

◇-elim : Run B → (A →̇ B) → ◇ A →̇ B
◇-elim rB f = rB ∘ ◇-map f

◇-elim! : Run B → ⟨ □ (A ⇒̂ B) ⊙ ◇ A ⟩→̇ B
◇-elim! rB f = rB ∘ ◇-map! f

◇-elim-□ : Run B → ⟨ □ (A ⇒̂ B) ⊙ □ (◇ A) ⟩→̇ □ B
◇-elim-□ rB f c = □-map (uncurry (◇-elim! rB)) (□-pair (□-mon f) c)

◇-elim-□-alt : Run B → ⟨ □ (A ⇒̂ B) ⊙ □ (◇ A) ⟩→̇ □ B
◇-elim-□-alt rB f c τ = ◇-elim! rB (□-mon f τ) (c τ)

bind! : Mon C → Run B → (C →̇ ◇ A) → (C →̇ (A ⇒̂ B)) → C →̇ B
bind! mC rB f k γ = ◇-elim! rB (λ τ a → k (mC γ τ) a) (f γ)

-- Type interpretation
------------------------------------------------------------------------

postulate
  ⟦_⟧ᵒ : Base → ISet
  monᵒ : ∀ o → Mon ⟦ o ⟧ᵒ

mutual
  ⟦_⟧⁺ : Ty⁺ → ISet
  ⟦ base o  ⟧⁺ = base o ∈_
  -- ⟦ base o  ⟧⁺ = ⟦ o ⟧ᵒ
  ⟦ P₁ ×̇ P₂ ⟧⁺ = ⟦ P₁ ⟧⁺ ×̂ ⟦ P₂ ⟧⁺
  ⟦ Σ̇ I P   ⟧⁺ = Σ̂ I λ i → ⟦ P i ⟧⁺
  ⟦ □̇ N     ⟧⁺ = □ ⟦ N ⟧⁻

  ⟦_⟧⁻ : Ty⁻ → ISet
  ⟦ ◇̇ P   ⟧⁻ = ◇ ⟦ P ⟧⁺
  ⟦ Π̇ I N ⟧⁻ = Π̂ I λ i → ⟦ N i ⟧⁻
  ⟦ P ⇒̇ N ⟧⁻ = ⟦ P ⟧⁺ ⇒̂ ⟦ N ⟧⁻

⟦_⟧ᶜ : Cxt → ISet
⟦_⟧ᶜ Γ Δ = All (λ P → ⟦ P ⟧⁺ Δ) Γ

-- ⟦ []    ⟧ᶜ = 1̂
-- ⟦ P ∷ Γ ⟧ᶜ = ⟦ Γ ⟧ᶜ ×̂ ⟦ P ⟧⁺

-- Positive types are monotone.

mon⁺ : (P : Ty⁺) → Mon ⟦ P ⟧⁺
mon⁺ (base o)  = monVar
mon⁺ (P₁ ×̇ P₂) = ×-mon (mon⁺ P₁) (mon⁺ P₂)
mon⁺ (Σ̇ I P)   = Σ-mon (mon⁺ ∘ P)
mon⁺ (□̇ N)     = □-mon

monᶜ : (Γ : Cxt) → Mon ⟦ Γ ⟧ᶜ
monᶜ Γ γ τ = All.map (λ {P} v → mon⁺ P v τ) γ

-- Negative types are runnable.

run⁻ : (N : Ty⁻) → Run ⟦ N ⟧⁻
run⁻ (◇̇ P)   = ◇-run
run⁻ (Π̇ I N) = Π-run (run⁻ ∘ N)
run⁻ (P ⇒̇ N) = ⇒-run (mon⁺ P) (run⁻ N)

-- monᶜ []      = 1-mon
-- monᶜ (P ∷ Γ) = ×-mon (monᶜ Γ) (mon⁺ P)

-- Interpretation
------------------------------------------------------------------------

mutual

  ⦅_⦆⁺ : Val P Γ → ⟦ Γ ⟧ᶜ →̇ ⟦ P ⟧⁺
  ⦅ var x ⦆⁺      = λ γ → All.lookup γ x
  ⦅ pair v₁ v₂ ⦆⁺ = < ⦅ v₁ ⦆⁺ , ⦅ v₂ ⦆⁺ >
  ⦅ inj i v ⦆⁺    = (i ,_) ∘ ⦅ v ⦆⁺
  ⦅ thunk t ⦆⁺    = □-intro (monᶜ _) ⦅ t ⦆⁻
  -- ⦅ thunk t ⦆⁺      = □-map ⦅ t ⦆⁻ ∘ monᶜ _

  λ⦅_⦆⁻ : Comp N (P ∷ Γ) → ⟦ Γ ⟧ᶜ →̇ ⟦ P ⇒̇ N ⟧⁻
  λ⦅ t ⦆⁻ γ a = ⦅ t ⦆⁻ (a ∷ γ)

  ⦅_⦆⁻ : Comp N Γ → ⟦ Γ ⟧ᶜ →̇ ⟦ N ⟧⁻
  ⦅ ret v ⦆⁻ = return ∘ ⦅ v ⦆⁺
  ⦅ rec t ⦆⁻ = flip λ i → ⦅ t i ⦆⁻
  ⦅ abs t ⦆⁻ = λ⦅ t ⦆⁻
  ⦅ split v t ⦆⁻ γ = let (a₁ , a₂) = ⦅ v ⦆⁺ γ in ⦅ t ⦆⁻ (a₂ ∷ (a₁ ∷ γ))
  ⦅ case v t ⦆⁻  γ = let (i , a) = ⦅ v ⦆⁺ γ in  ⦅ t i ⦆⁻ (a ∷ γ)
  ⦅ bind {Γ = Γ} {N = N} t t₁ ⦆⁻ = bind! (monᶜ Γ) (run⁻ N) ⦅ t ⦆⁻ λ⦅ t₁ ⦆⁻
  -- ⦅ bind {N = N} t t₁ ⦆⁻ γ = ◇-elim! (run⁻ N) (λ τ a → ⦅ t₁ ⦆⁻ (a ∷ monᶜ _ γ τ)) (⦅ t ⦆⁻ γ)
  -- ⦅ bind {N = N} t t₁ ⦆⁻ γ = ◇-elim (run⁻ N) {!λ a → ⦅ t₁ ⦆⁻ (a ∷ γ)!} (⦅ t ⦆⁻ γ)
  -- ⦅ bind {N = N} t t₁ ⦆⁻ =  ⦅ t₁ ⦆⁻ ∘ λ γ → {!!} ∷ γ
  -- ⦅ bind {N = N} t t₁ ⦆⁻ =  ⦅ t₁ ⦆⁻ ∘ {! ◇-elim (run⁻ N) {!(_∷ _)!} ∘ ⦅ t ⦆⁻ !}
  -- ⦅ bind t t₁ ⦆⁻ = {!◇-elim ? ∘ ⦅ t ⦆⁻ !}
  ⦅ force v ⦆⁻  = extract ∘ ⦅ v ⦆⁺
  ⦅ prj i t ⦆⁻  = (_$ i) ∘ ⦅ t ⦆⁻
  ⦅ app t v ⦆⁻  = ⦅ t ⦆⁻  ˢ ⦅ v ⦆⁺
  ⦅ letv v t ⦆⁻ = λ⦅ t ⦆⁻ ˢ ⦅ v ⦆⁺
  -- ⦅ letv v t ⦆⁻ γ = ⦅ t ⦆⁻ (⦅ v ⦆⁺ γ ∷ γ)

  -- rec⦅_⦆⁻ : (∀ i → Comp (Ns i) Γ) → ⟦ Γ ⟧ᶜ →̇ Π̂ I λ i → ⟦ Ns i ⟧⁻
  -- rec⦅ t ⦆⁻ γ i = ⦅ t i ⦆⁻ γ

-- Reflection and reification

mutual
  -- fresh : ∀ {P Γ} → ◇ ⟦ P ⟧⁺ (P ∷ Γ)
  -- fresh□ : ∀ {P Γ} → □ (⟨ P ⟩ (◇ ⟦ P ⟧⁺)) Γ

  fresh□◇□ : ∀ P {Γ} → ⟨ P ⟩ (□ (◇ (□ ⟦ P ⟧⁺))) Γ
  fresh□◇□ P = reflect⁺□ P ∘ monVar here!

  fresh□ : ∀ P {Γ} → ⟨ P ⟩ (□ (◇ ⟦ P ⟧⁺)) Γ
  fresh□ P = ◇-map extract ∘ reflect⁺□ P ∘ monVar here!
  fresh□ P = reflect⁺ P ∘ monVar here!

  fresh : ∀ {P Γ} → ⟨ P ⟩ (◇ ⟦ P ⟧⁺) Γ
  fresh {P} = ◇-map extract (reflect⁺□ P here!)
  fresh {P} = reflect⁺ P here!

  fresh◇ : ∀ {P Γ} → ⟨ P ⟩ (◇ (□ ⟦ P ⟧⁺)) Γ
  fresh◇ {P} = reflect⁺□ P here!
  fresh◇ {P} = ◇-map (mon⁺ P) fresh

  -- saves us use of Mon P in freshᶜ
  reflect⁺□ : (P : Ty⁺) → (P ∈_) →̇ (◇ (□ ⟦ P ⟧⁺))
  reflect⁺□ (base o)  x = return (monVar x)
  reflect⁺□ (P₁ ×̇ P₂) x = split x (◇□-pair (reflect⁺□ P₁ ∘ monVar (there here!)) fresh◇)
  reflect⁺□ (Σ̇ I Ps)  x = case x λ i → ◇-map (□-map (i ,_)) fresh◇
  reflect⁺□ (□̇ N)     x = return (□-mon (reflect⁻ N ∘ force ∘ monVar x))

  reflect⁺ : (P : Ty⁺) → (P ∈_) →̇ (◇ ⟦ P ⟧⁺)
  reflect⁺ (base o)  x = return x
  reflect⁺ (P₁ ×̇ P₂) x = split x (□-weak (fresh□ P₁) ⋉ fresh◇)
  reflect⁺ (P₁ ×̇ P₂) x = split x (◇-pair (□-weak (fresh□ P₁)) fresh◇)
  reflect⁺ (P₁ ×̇ P₂) x = split x (◇-pair (□-weak (fresh□ P₁)) (◇-map (mon⁺ P₂) (fresh {P₂})))
  reflect⁺ (P₁ ×̇ P₂) x = split x (◇-pair (fresh□ P₁ ∘ ⊆-trans (P₂ ∷ʳ ⊆-refl)) (◇-map (mon⁺ P₂) (fresh {P₂})))
  reflect⁺ (P₁ ×̇ P₂) x = split x (join $ ◇-map! (λ τ a₂ → ◇-map! (λ τ′ a₁ → a₁ , mon⁺ P₂ a₂ τ′) (fresh□ P₁ (⊆-trans (_ ∷ʳ ⊆-refl) τ))) (fresh {P₂}))
  reflect⁺ (Σ̇ I Ps)  x = case x λ i → ◇-map (i ,_) fresh
  reflect⁺ (□̇ N)     x = return λ τ → reflect⁻ N (force (monVar x τ))

  reflect⁻ : (N : Ty⁻) → Ne N →̇ ⟦ N ⟧⁻
  reflect⁻ (◇̇ P)    u = bind u fresh
  reflect⁻ (Π̇ I Ns) u = λ i → reflect⁻ (Ns i) (prj i u)
  reflect⁻ (P ⇒̇ N)  u = λ a → reflect⁻ N (app u (reify⁺ P a))

  reify⁺ : (P : Ty⁺) → ⟦ P ⟧⁺ →̇ NVal P
  reify⁺ (base o) = var
  reify⁺ (P₁ ×̇ P₂) (a₁ , a₂) = pair (reify⁺ P₁ a₁) (reify⁺ P₂ a₂)
  reify⁺ (Σ̇ I Ps)  (i  , a ) = inj i (reify⁺ (Ps i) a)
  reify⁺ (□̇ N) a = thunk (reify⁻ N a)

  reify⁻ : (N : Ty⁻) → □ ⟦ N ⟧⁻ →̇ Nf N
  reify⁻ (◇̇ P)    f = ret (◇-map (reify⁺ P) (extract f))
  reify⁻ (Π̇ I Ns) f = rec λ i → reify⁻ (Ns i) (□-map (_$ i) f)
  reify⁻ (P ⇒̇ N)  f = abs $ reify⁻ N $ ◇-elim-□ (run⁻ N) (□-weak f) (fresh□ P)

  reify⁻ (P ⇒̇ N)  f = abs $ reify⁻ N λ τ →
    ◇-elim! (run⁻ N)
      (□-mon (□-weak f) τ) -- (□-mon f (⊆-trans (_ ∷ʳ ⊆-refl) τ))
      (fresh□ P τ) -- (reflect⁺ P (monVar here! τ))
 -- (□-map {!◇-elim! (run⁻ N) ? fresh!})
  -- reify⁻ (P ⇒̇ N)  f = abs (reify⁻ N {!◇-elim! (run⁻ N) ? fresh!})
-- (run⁻ N (□-map {!!} (□-weak f)) fresh))

ext : (⟦ Γ ⟧ᶜ ×̂ ⟦ P ⟧⁺) →̇ ⟦ P ∷ Γ ⟧ᶜ
ext (γ , a) = a ∷ γ

◇-ext : ◇ (⟦ Γ ⟧ᶜ ×̂ ⟦ P ⟧⁺) →̇ ◇ ⟦ P ∷ Γ ⟧ᶜ
◇-ext = ◇-map ext

-- Without the use of ◇-mon!

freshᶜ : (Γ : Cxt) → □ (◇ ⟦ Γ ⟧ᶜ) Γ
freshᶜ []      = λ τ → return []
freshᶜ (P ∷ Γ) = ◇-ext ∘ □◇-pair' (□-weak (freshᶜ Γ)) (fresh□◇□ P)
freshᶜ (P ∷ Γ) = ◇-ext ∘ □◇-pair (mon⁺ P) (□-weak (freshᶜ Γ)) (fresh□ P)
freshᶜ (P ∷ Γ) = ◇-ext ∘ □◇-pair' (□-weak (freshᶜ Γ)) (◇-map (mon⁺ P) ∘ (fresh□ P))
-- freshᶜ (P ∷ Γ) = λ τ → ◇-ext $
freshᶜ (P ∷ Γ) = ◇-ext ∘ λ τ →
  (□-weak (□-mon (freshᶜ Γ)) τ)
  ⋉ ◇-map (mon⁺ P) (fresh□ P τ)
freshᶜ (P ∷ Γ) = λ τ → ◇-ext $
  (□-mon (freshᶜ Γ) (⊆-trans ((_ ∷ʳ ⊆-refl)) τ))
  ⋉ ◇-map (mon⁺ P) (fresh□ P τ)

--  ⋉ ◇-map (mon⁺ P) (reflect⁺ P (monVar here! τ)))

norm : Comp N →̇ Nf N
norm {N = N} {Γ = Γ} t = reify⁻ N $ □-map (run⁻ N ∘ ◇-map ⦅ t ⦆⁻) $ freshᶜ Γ
norm {N = N} {Γ = Γ} t = reify⁻ N $ run⁻ N ∘ ◇-map ⦅ t ⦆⁻ ∘ freshᶜ Γ

-- norm {N = N} t = reify⁻ N (run⁻ N ∘ ◇-map ⦅ t ⦆⁻ ∘ freshG)
-- norm {N = N} t = reify⁻ N λ τ → run⁻ N $ (◇-map ⦅ t ⦆⁻ $ (freshG τ))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
