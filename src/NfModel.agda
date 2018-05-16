-- A Beth model of normal forms

open import Library

module NfModel (Base : Set) where

import Formulas   ; open module Form = Formulas    Base
import Derivations; open module Der  = Derivations Base


-- Beth model

data Cover (Δ : Cxt) : Set where
  idc  : Cover Δ
  bot  : (t : Ne Δ False) → Cover Δ
  node : ∀{A B} (t : Ne Δ (A ∨ B)) (C : Cover (Δ ∙ A)) (D : Cover (Δ ∙ B)) → Cover Δ

data _∈_ Γ : ({Δ} : Cxt) (C : Cover Δ) → Set where
  here  : Γ ∈ idc {Γ}
  left  : ∀{Δ A B C D} {t : Ne Δ (A ∨ B)} (e : Γ ∈ C) → Γ ∈ node t C D
  right : ∀{Δ A B C D} {t : Ne Δ (A ∨ B)} (e : Γ ∈ D) → Γ ∈ node t C D

coverWk : ∀{Γ Δ} {C : Cover Δ} (e : Γ ∈ C) → Γ ≤ Δ
coverWk here      = id≤
coverWk (left  e) = coverWk e • weak id≤
coverWk (right e) = coverWk e • weak id≤

transC : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → Cover Δ) → Cover Γ
transC idc f = f here
transC (bot t) f = bot t
transC (node t C D) f = node t (transC C (f ∘ left)) (transC D (f ∘ right))

-- UNUSED:
trans∈ : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → Cover Δ) →
  ∀ {Φ} {Δ} (e : Δ ∈ C) → Φ ∈ f e → Φ ∈ transC C f
trans∈ idc f here = id
trans∈ (bot t) f ()
trans∈ (node t C D) f (left  e) = left  ∘ trans∈ C (f ∘ left ) e
trans∈ (node t C D) f (right e) = right ∘ trans∈ D (f ∘ right) e

split∈ : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → Cover Δ) {Φ} (e : Φ ∈ transC C f)
  → ∃ λ Δ → ∃ λ (e : Δ ∈ C) → Φ ∈ f e
split∈ idc f e = _ , _ , e
split∈ (bot t) f ()
split∈ (node t C D) f (left e) with split∈ C (f ∘ left) e
... | Δ , e₁ , e₂ = Δ , left e₁ , e₂
split∈ (node t C D) f (right e) with split∈ D (f ∘ right) e
... | Δ , e₁ , e₂ = Δ , right e₁ , e₂

-- Empty cover

EmptyCover : (Γ : Cxt) → Set
EmptyCover Γ = Σ (Cover Γ) λ C → ∀{Δ} → Δ ∈ C → ⊥

-- Empty cover is isomorphic to a witness of inconsistency

toEmptyCover : ∀{Γ} (t : Ne Γ False) → EmptyCover Γ
toEmptyCover t = bot t , λ()

fromEmptyCover : ∀{Γ} (ec : EmptyCover Γ) → Nf Γ False
fromEmptyCover (C , f) = reifyF C f
  where
  reifyF : ∀ {Γ} (C : Cover Γ) (f : ∀ {Δ} → Δ ∈ C → ⊥) → Nf Γ False
  reifyF idc          f = ⊥-elim (f here)
  reifyF (bot t)      f = ne t
  reifyF (node t C D) f = orE t (reifyF C (f ∘ left)) (reifyF D (f ∘ right))

transE : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → EmptyCover Δ) → EmptyCover Γ
transE C f = transC C (proj₁ ∘ f) , λ e → let _ , e₁ , e₂ = split∈ C (proj₁ ∘ f) e in f e₁ .proj₂ e₂

-- Syntactic paste (from Thorsten)

paste' : ∀{A Γ} (C : Cover Γ) (f : ∀{Δ} (e : Δ ∈ C) → Nf Δ A) → Nf Γ A
paste' idc          f = f here
paste' (bot t)      f = falseE t
paste' (node t C D) f = orE t (paste' C (f ∘ left)) (paste' D (f ∘ right))

-- Weakening Covers

monC : ∀{Γ Δ} (τ : Δ ≤ Γ) (C : Cover Γ) → Cover Δ
monC τ idc = idc
monC τ (bot t) = bot (monNe τ t)
monC τ (node t C D) = node (monNe τ t) (monC (lift τ) C) (monC (lift τ) D)

mon∈ : ∀{Γ Δ Φ} (C : Cover Γ) (τ : Δ ≤ Γ) (e : Φ ∈ monC τ C) → ∃ λ Ψ → Ψ ∈ C × Φ ≤ Ψ
mon∈ {Γ} {Δ} {.Δ} idc τ here = _ , here , τ
mon∈ {Γ} {Δ} {Φ} (bot t) τ ()
mon∈ {Γ} {Δ} {Φ} (node t C D) τ (left e) with mon∈ C (lift τ) e
... | Ψ , e' , σ = Ψ , left e' , σ
mon∈ {Γ} {Δ} {Φ} (node t C D) τ (right e) with mon∈ D (lift τ) e
... | Ψ , e' , σ = Ψ , right e' , σ

-- The syntactic Beth model

T⟦_⟧ : (A : Form) (Γ : Cxt) → Set
T⟦ Atom P ⟧ Γ = Nf Γ (Atom P)
T⟦ True ⟧ Γ = ⊤
T⟦ False ⟧ Γ = EmptyCover Γ
T⟦ A ∨ B ⟧ Γ = ∃ λ (C : Cover Γ) → ∀{Δ} → Δ ∈ C → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ
T⟦ A ∧ B ⟧ Γ = T⟦ A ⟧ Γ × T⟦ B ⟧ Γ
T⟦ A ⇒ B ⟧ Γ = ∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ B ⟧ Δ

monT : ∀ A {Γ Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ → T⟦ A ⟧ Δ
monT (Atom P) τ t = monNf τ t
monT True τ _ = _
monT False τ (C , f) = monC τ C , λ {Φ} e → f (proj₁ (proj₂ (mon∈ C τ e)))
monT (A ∨ B) {Γ} {Δ} τ (C , f) = monC τ C ,  λ {Φ} e →
  let Ψ , e' , σ = mon∈ C τ e
  in  map-⊎ (monT A σ) (monT B σ) (f {Ψ} e')
monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
monT (A ⇒ B) τ f σ = f (σ • τ)

-- Reflection / reification

mutual

  reflect : ∀{Γ} A (t : Ne Γ A) → T⟦ A ⟧ Γ
  reflect (Atom P) t = ne t
  reflect True t = _
  reflect False = toEmptyCover
  reflect (A ∨ B) t = node t idc idc , aux
    where
    aux : ∀{Δ} → Δ ∈ node t idc idc → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ
    aux (left  here) = inj₁ (reflect A (hyp top))
    aux (right here) = inj₂ (reflect B (hyp top))

  reflect (A ∧ B) t = reflect A (andE₁ t) , reflect B (andE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (impE (monNe τ t) (reify A a))

  reify : ∀{Γ} A (⟦f⟧ :  T⟦ A ⟧ Γ) → Nf Γ A
  reify (Atom P) t      = t
  reify True _          = trueI
  reify False           = fromEmptyCover
  reify (A ∨ B) (C , f) = paste' C ([ orI₁ ∘ reify A , orI₂ ∘ reify B ] ∘ f)
  reify (A ∧ B) (a , b) = andI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = impI (reify B (⟦f⟧ (weak id≤) (reflect A (hyp top))))

-- Semantic paste

paste : ∀ A {Γ} (C : Cover Γ) (f : ∀{Δ} (e : Δ ∈ C) → T⟦ A ⟧ Δ) → T⟦ A ⟧ Γ
paste (Atom P) = paste'
paste True C f = _
paste False C f = transE C f
paste (A ∨ B) C f = transC C (proj₁ ∘ f) , λ e → let _ , e₁ , e₂ = split∈ C (proj₁ ∘ f) e in f e₁ .proj₂ e₂
paste (A ∧ B) C f = paste A C (proj₁ ∘ f) , paste B C (proj₂ ∘ f)
paste (A ⇒ B) C f τ a = paste B (monC τ C) λ {Δ} e → let Ψ , e' , σ  = mon∈ C τ e in f e' σ (monT A (coverWk e) a)

-- Fundamental theorem

-- Extension of T⟦_⟧ to contexts

G⟦_⟧ : ∀ (Γ Δ : Cxt) → Set
G⟦ ε     ⟧ Δ = ⊤
G⟦ Γ ∙ A ⟧ Δ = G⟦ Γ ⟧ Δ × T⟦ A ⟧ Δ

monG : ∀{Γ Δ Φ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ → G⟦ Γ ⟧ Φ
monG {ε} τ _ = _
monG {Γ ∙ A} τ (γ , a) = monG τ γ , monT A τ a

-- Variable case

fundH : ∀{Γ Δ A} (x : Hyp Γ A) (γ : G⟦ Γ ⟧ Δ) → T⟦ A ⟧ Δ
fundH top     = proj₂
fundH (pop x) = fundH x ∘ proj₁

-- A lemma for the orE case

orElim : ∀ {Γ A B X} (C : Cover Γ) (f : {Δ : Cxt} → Δ ∈ C → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ) →
         (∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ X ⟧ Δ) →
         (∀{Δ} (τ : Δ ≤ Γ) → T⟦ B ⟧ Δ → T⟦ X ⟧ Δ) →
         T⟦ X ⟧ Γ
orElim C f g h = paste _ C λ e → [ g (coverWk e) , h (coverWk e) ] (f e)

-- A lemma for the falseE case

falseElim : ∀{Γ A} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → ⊥) → T⟦ A ⟧ Γ
falseElim C f = paste _ C (⊥-elim ∘ f)

-- The fundamental theorem

fund :  ∀{Γ A} (t : Γ ⊢ A) {Δ} (γ : G⟦ Γ ⟧ Δ) → T⟦ A ⟧ Δ
fund (hyp x) = fundH x
fund (impI t) γ τ a = fund t (monG τ γ , a)
fund (impE t u) γ = fund t γ id≤ (fund u γ)
fund (andI t u) γ = fund t γ , fund u γ
fund (andE₁ t) = proj₁ ∘ fund t
fund (andE₂ t) = proj₂ ∘ fund t
fund (orI₁ t) γ = idc , inj₁ ∘ λ{ here → fund t γ }
fund (orI₂ t) γ = idc , inj₂ ∘ λ{ here → fund t γ }
fund (orE t u v) γ = uncurry orElim (fund t γ)
  (λ τ a → fund u (monG τ γ , a))
  (λ τ b → fund v (monG τ γ , b))
fund (falseE t) γ = uncurry falseElim (fund t γ)
fund trueI γ = _

-- Identity environment

ide : ∀ Γ → G⟦ Γ ⟧ Γ
ide ε = _
ide (Γ ∙ A) = monG (weak id≤) (ide Γ) , reflect A (hyp top)

-- Normalization

norm : ∀{Γ A} (t : Γ ⊢ A) → Nf Γ A
norm t = reify _ (fund t (ide _))

-- -}
-- -}
