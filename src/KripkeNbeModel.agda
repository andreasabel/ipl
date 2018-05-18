{-# OPTIONS --rewriting #-}

-- A Beth model of normal forms

open import Library

module KripkeNbeModel (Base : Set) (B⦅_⦆ : Base → Set) where

import Formulas      ; open module Form = Formulas    Base
import Derivations   ; open module Der  = Derivations Base
import Interpretation; open module Intp = Interpretation Base B⦅_⦆

NeImg : (Γ : Cxt) (A : Form) (f : Fun Γ A) → Set
NeImg Γ A f = ∃ λ (t : Ne Γ A) → Ne⦅ t ⦆ ≡ f

NfImg : (Γ : Cxt) (A : Form) (f : Fun Γ A) → Set
NfImg Γ A f = ∃ λ (t : Nf Γ A) → Nf⦅ t ⦆ ≡ f

monNeImg : ∀{Γ Δ} (τ : Δ ≤ Γ) {A f} (nei : NeImg Γ A f) → NeImg Δ A (f ∘ R⦅ τ ⦆)
monNeImg τ (t , refl) = monNe τ t , natD τ (ne[ t ])

monNfImg : ∀{Γ Δ} (τ : Δ ≤ Γ) {A f} (nfi : NfImg Γ A f) → NfImg Δ A (f ∘ R⦅ τ ⦆)
monNfImg τ (t , refl) = monNf τ t , natD τ nf[ t ]

iNe : ∀{Γ P f} → NeImg Γ (Atom P) f → NfImg Γ (Atom P) f
iNe (t , eq) = ne t , eq

-- iNe : ∀{Γ A f} → NeImg Γ A f → NfImg Γ A f
-- iNe (t , eq) = ne t , eq

iHyp : ∀{Γ A} (x : Hyp Γ A) → NeImg Γ A H⦅ x ⦆
iHyp x = (hyp x , refl)

iImpI : ∀{Γ A B f} → NfImg (Γ ∙ A) B f → NfImg Γ (A ⇒ B) (curry f)
iImpI (t , eq) = impI t , cong curry eq

iImpE : ∀{Γ A B f g} → NeImg Γ (A ⇒ B) f → NfImg Γ A g → NeImg Γ B (apply f g)
iImpE (t , eq) (u , eq') = (impE t u , cong₂ apply eq eq')

iAndE₁ : ∀{Γ A B f} → NeImg Γ (A ∧ B) f → NeImg Γ A (proj₁ ∘ f)
iAndE₁ (t , eq) = andE₁ t , cong (proj₁ ∘_) eq

iAndE₂ : ∀{Γ A B f} → NeImg Γ (A ∧ B) f → NeImg Γ B (proj₂ ∘ f)
iAndE₂ (t , eq) = andE₂ t , cong (proj₂ ∘_) eq

iTrueI : ∀{Γ f} → NfImg Γ True f
iTrueI = trueI , refl

iAndI : ∀{Γ A B f g} → NfImg Γ A f → NfImg Γ B g → NfImg Γ (A ∧ B) < f , g >
iAndI (t , eq) (u , eq') = andI t u , cong₂ <_,_> eq eq'

iOrI₁ : ∀{Γ A B f} → NfImg Γ A f → NfImg Γ (A ∨ B) (inj₁ ∘ f)
iOrI₁ (t , eq) = orI₁ t , cong (inj₁ ∘_) eq

iOrI₂ : ∀{Γ A B f} → NfImg Γ B f → NfImg Γ (A ∨ B) (inj₂ ∘ f)
iOrI₂ (t , eq) = orI₂ t , cong (inj₂ ∘_) eq

⊥-ext : ∀ {x y : ⊥} {a} {A : Set a} (f : ⊥ → A) → f x ≡ f y
⊥-ext {}

-- ⊥-elim-ext-app : ∀{a b} {A : Set a} {B : Set b} {f : A → ⊥} {g : B → ⊥) {h : A → B}
--   → ⊥-elim {b} {B} ∘ f ≡ ⊥-elim g ∘ h


iFalseE : ∀{Γ A f S} {g : S → T⦅ A ⦆} → NeImg Γ False f → NfImg Γ A (g ∘ ⊥-elim ∘ f)
iFalseE (t , refl) = falseE t , ⊥-elim-ext

iFalseE' : ∀{A Γ} (t : Nf Γ False) → NfImg Γ A (⊥-elim ∘ Nf⦅ t ⦆)
-- iFalseE' (ne t) = falseE t , refl   -- only for η-oblivious nfs
iFalseE' {A} (orE t t₁ t₂) with iFalseE' {A} t₁ | iFalseE' {A} t₂
... | u , eq | v , eq' = orE t u v , sym ⊥-elim-ext
iFalseE' (falseE t) = falseE t , ⊥-elim-ext

iFalseE! : ∀{Γ A f} → NfImg Γ False f → NfImg Γ A (⊥-elim ∘ f)
iFalseE! (t , refl) = iFalseE' t

-- The Kripke model

mutual

  T⟦_⟧ : (A : Form) (Γ : Cxt) (f : Fun Γ A) → Set
  T⟦ Atom P ⟧ Γ = NfImg Γ (Atom P)
  T⟦ True ⟧ Γ _ = ⊤
  T⟦ False ⟧ Γ = NfImg Γ False
  T⟦ A ∨ B ⟧ Γ = Disj A B Γ
  T⟦ A ∧ B ⟧ Γ f = T⟦ A ⟧ Γ (proj₁ ∘ f) × T⟦ B ⟧ Γ (proj₂ ∘ f)
  T⟦ A ⇒ B ⟧ Γ f = ∀{Δ} (τ : Δ ≤ Γ) {a : Fun Δ A} (⟦a⟧ : T⟦ A ⟧ Δ a) → T⟦ B ⟧ Δ (kapp {A = A} {B = B} f τ a)

  {-# NO_POSITIVITY_CHECK #-}
  data Disj (A B : Form) (Γ : Cxt) (f : Fun Γ (A ∨ B)) : Set where
    ne    : (ine : NeImg Γ (A ∨ B) f) → Disj A B Γ f
    left  : (g : Fun Γ A) (eq : inj₁ ∘ g ≡ f) (⟦g⟧ : T⟦ A ⟧ Γ g) → Disj A B Γ f
    right : (g : Fun Γ B) (eq : inj₂ ∘ g ≡ f) (⟦g⟧ : T⟦ B ⟧ Γ g) → Disj A B Γ f

mutual
  monT : ∀ A {Γ Δ} {f : Fun Γ A} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ f → T⟦ A ⟧ Δ (f ∘ R⦅ τ ⦆)
  monT (Atom P) τ = monNfImg τ
  monT True τ _ = _
  monT False τ = monNfImg τ
  monT (A ∨ B) τ = monDisj A B τ
  monT (A ∧ B) τ = monT A τ ×̇ monT B τ
  monT (A ⇒ B) τ f σ = f (σ • τ)

  monDisj : ∀ A B {Γ Δ} {f : Fun Γ (A ∨ B)} (τ : Δ ≤ Γ) → Disj A B Γ f → Disj A B Δ (f ∘ R⦅ τ ⦆)
  monDisj A B τ (ne ine) = ne (monNeImg τ ine)
  monDisj A B τ (left  g eq ⟦g⟧) = left  (g ∘ R⦅ τ ⦆) (cong (_∘ R⦅ τ ⦆) eq) (monT A τ ⟦g⟧)
  monDisj A B τ (right g eq ⟦g⟧) = right (g ∘ R⦅ τ ⦆) (cong (_∘ R⦅ τ ⦆) eq) (monT B τ ⟦g⟧)

-- Reflection / reification

mutual

  reflect : ∀{Γ} A {f} (t : NeImg Γ A f) → T⟦ A ⟧ Γ f
  reflect (Atom P) t = iNe t
  reflect True t = _
  reflect False t = iFalseE t
  reflect (A ∨ B) t = ne t
{-
    where
    aux : ∀{Δ} → Δ ∈ node t idc idc → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ
    aux (left  here) = inj₁ (reflect A (hyp top))
    aux (right here) = inj₂ (reflect B (hyp top))
-}
  reflect (A ∧ B) t = reflect A (iAndE₁ t) , reflect B (iAndE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (iImpE (monNeImg τ t) (reify A a))

  reify : ∀{Γ} A {f} (⟦f⟧ : T⟦ A ⟧ Γ f) → NfImg Γ A f
  reify (Atom P) t      = t
  reify True _          = iTrueI
  reify False {f} t     = t
  reify (A ∨ B)         = reifyDisj A B
  reify (A ∧ B) (a , b) = iAndI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = iImpI (reify B (⟦f⟧ (weak id≤) (reflect A (iHyp top))))

  reifyDisj : ∀ A B {Γ} {f} → Disj A B Γ f → NfImg Γ (A ∨ B) f
  reifyDisj A B (ne ine) = {! iNe ine !}
  reifyDisj A B (left  g refl ⟦g⟧) = iOrI₁ (reify A ⟦g⟧)
  reifyDisj A B (right g refl ⟦g⟧) = iOrI₂ (reify B ⟦g⟧)

-- Fundamental theorem

-- Extension of T⟦_⟧ to contexts

G⟦_⟧ : ∀ (Γ Δ : Cxt) (ρ : Mor Δ Γ) → Set
G⟦ ε     ⟧ Δ ρ = ⊤
G⟦ Γ ∙ A ⟧ Δ ρ = G⟦ Γ ⟧ Δ (proj₁ ∘ ρ) × T⟦ A ⟧ Δ (proj₂ ∘ ρ)

monG : ∀{Γ Δ Φ ρ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ ρ → G⟦ Γ ⟧ Φ (ρ ∘ R⦅ τ ⦆)
monG {ε} τ _ = _
monG {Γ ∙ A} τ (γ , a) = monG τ γ , monT A τ a

-- Variable case

fundH : ∀{Γ Δ A ρ} (x : Hyp Γ A) (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (H⦅ x ⦆ ∘ ρ)
fundH top     = proj₂
fundH (pop x) = fundH x ∘ proj₁

-- A lemma for the orE case

paste : ∀ X {Γ A B} {g h} (t : Ne Γ (A ∨ B)) →
         T⟦ A ⇒ X ⟧ Γ (curry g) →
         T⟦ B ⇒ X ⟧ Γ (curry h) →
         T⟦ X ⟧ Γ (caseof Ne⦅ t ⦆ g h)
-- paste X t ⟦g⟧ ⟦h⟧ = {!!}  -- Here I would need something more than t : Ne Γ (A ∨ B), like a Cover?
paste (Atom P) {Γ} {A} {B} t ⟦g⟧ ⟦h⟧
  with ⟦g⟧ (weak id≤) (reflect A (iHyp top))
     | ⟦h⟧ (weak id≤) (reflect B (iHyp top))
... | u , refl | v , refl = orE t u v , refl
paste True t ⟦g⟧ ⟦h⟧ = _
paste False {Γ} {A} {B} t ⟦g⟧ ⟦h⟧
  with ⟦g⟧ (weak id≤) (reflect A (iHyp top))
     | ⟦h⟧ (weak id≤) (reflect B (iHyp top))
... | u , refl | v , refl = orE t u v , refl
paste (X ∨ Y) t ⟦g⟧ ⟦h⟧ = {!!}  -- Here I would need something more than t : Ne Γ (A ∨ B), like a Cover?
paste (X ∧ Y) t ⟦g⟧ ⟦h⟧ = {!!}
paste (X ⇒ Y) t ⟦g⟧ ⟦h⟧ = {!!}


orElim : ∀ X {Γ A B} {f g h } → Disj A B Γ f →
         T⟦ A ⇒ X ⟧ Γ (curry g) →
         T⟦ B ⇒ X ⟧ Γ (curry h) →
         T⟦ X ⟧ Γ (caseof f g h)
orElim X (ne (t , refl)) ⟦g⟧ ⟦h⟧ = paste X t ⟦g⟧ ⟦h⟧
orElim X (left  a refl ⟦a⟧) ⟦g⟧ ⟦h⟧ = ⟦g⟧ id≤ ⟦a⟧
orElim X (right b refl ⟦b⟧) ⟦g⟧ ⟦h⟧ = ⟦h⟧ id≤ ⟦b⟧

-- A lemma for the falseE case

-- falseElim : ∀ A {Γ f} {S : Set} (g : S → T⦅ A ⦆) → T⟦ False ⟧ Γ f → T⟦ A ⟧ Γ (g ∘ ⊥-elim ∘ f)
-- falseElim (Atom P) g t = {! iFalseE t !}
-- falseElim True g t = _
-- falseElim False g (t , refl) = t , funExt λ _ → ⊥-ext
-- falseElim (A ∨ B) g t = left {!!} {!!} (falseElim A id t)
-- falseElim (A ∧ B) g t = falseElim A (proj₁ ∘ g) t ,  falseElim B (proj₂ ∘ g) t
-- falseElim (A ⇒ B) g t = {!!}
-- -- reflect A (iFalseE t)

falseElim : ∀ A {Γ f} → T⟦ False ⟧ Γ f → T⟦ A ⟧ Γ (⊥-elim ∘ f)
falseElim (Atom P) t = iFalseE! t
falseElim True t = _
falseElim False (t , refl) = t , funExt λ _ → ⊥-ext id
falseElim (A ∨ B) t = left _ (sym ⊥-elim-ext) (falseElim A t)
falseElim (A ∧ B) t = subst (T⟦ A ⟧ _) ⊥-elim-ext (falseElim A t)
                    , subst (T⟦ B ⟧ _) ⊥-elim-ext (falseElim B t)
falseElim (A ⇒ B) t τ ⟦a⟧ = subst (T⟦ B ⟧ _) ⊥-elim-ext (falseElim B (monNfImg τ t))
  -- where
  -- aux : ∀{A B} (f ⊥-elim ∘ f = ⊥-elim ∘ apply f a
-- reflect A (iFalseE t)

-- The fundamental theorem

fund :  ∀{A Γ} (t : Γ ⊢ A) {Δ ρ} (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (D⦅ t ⦆ ∘ ρ)
fund (hyp x) = fundH x
fund (impI t) γ τ a = fund t (monG τ γ , a)
fund (impE t u) γ = fund t γ id≤ (fund u γ)
fund (andI t u) γ = fund t γ , fund u γ
fund (andE₁ t) = proj₁ ∘ fund t
fund (andE₂ t) = proj₂ ∘ fund t
fund (orI₁ t) γ = left  _ refl (fund t γ)
fund (orI₂ t) γ = right _ refl (fund t γ)
fund {A} (orE t u v) γ =  orElim A (fund t γ)
  (λ τ a → fund u (monG τ γ , a))
  (λ τ b → fund v (monG τ γ , b))
fund {A} (falseE t) γ = falseElim A (fund t γ)
fund trueI γ = _

-- Identity environment

ide : ∀ Γ → G⟦ Γ ⟧ Γ id
ide ε = _
ide (Γ ∙ A) = monG (weak id≤) (ide Γ) , reflect A (iHyp top)

-- Normalization

norm : ∀{Γ A} (t : Γ ⊢ A) → Nf Γ A
norm t = proj₁ (reify _ (fund t (ide _)))

-- -}
-- -}
