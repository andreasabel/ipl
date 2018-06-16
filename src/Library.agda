{-# OPTIONS --rewriting #-}

-- Interface to the standard library.
-- Place to add own auxiliary definitions.

module Library where

open import Data.Unit    public using (⊤)
open import Data.Empty   public using (⊥; ⊥-elim)
open import Data.Product public using (Σ; ∃; _×_; _,_; proj₁; proj₂; <_,_>; curry; uncurry) renaming (map to map-×)
open import Data.Sum     public using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′) renaming (map to map-⊎)
open import Function     public using (_∘_; _∘′_; id; _$_; case_of_; const)

open import Relation.Binary.PropositionalEquality public using (_≡_; refl; sym; trans; cong; cong₂; subst; Extensionality)
{-# BUILTIN REWRITE _≡_ #-}

postulate funExt : ∀{a b} → Extensionality a b

⊥-elim-ext : ∀{a b} {A : Set a} {B : Set b} {f : A → ⊥} {g : A → B} → ⊥-elim {b} {B} ∘ f ≡ g
⊥-elim-ext {f = f} = funExt λ a → ⊥-elim (f a)

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {a a' b b' c c'} → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

_×̇_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f ×̇ g) (x , y) = f x , g y

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)

caseof : ∀{A B C D : Set} (f : C → A ⊎ B) (g : C × A → D) (h : C × B → D) → C → D
caseof f g h = λ c → [ curry g c , curry h c ] (f c)

sum-eta : ∀{A B : Set} (x : A ⊎ B) → [ inj₁ , inj₂ ] x ≡ x
sum-eta (inj₁ x) = refl
sum-eta (inj₂ y) = refl

caseof-eta : ∀{A B C : Set} (f : C → A ⊎ B) → caseof f (inj₁ ∘ proj₂) (inj₂ ∘ proj₂) ≡ f
caseof-eta f = funExt λ c → sum-eta (f c)

sum-perm : ∀{A B C D : Set} (k : C → D) {g : A → C} {h : B → C} (x : A ⊎ B) →
  [ k ∘ g , k ∘ h ]′ x ≡ k ([ g , h ]′ x)
sum-perm k (inj₁ x) = refl
sum-perm k (inj₂ y) = refl

caseof-perm' : ∀{A B C D E : Set}
  (k : C → D → E) {f : C → A ⊎ B} {g : C × A → D} {h : C × B → D} →
  caseof f (apply (k ∘ proj₁) g) (apply (k ∘ proj₁) h)
    ≡ apply k (caseof f g h)
caseof-perm' k {f} = funExt λ c → sum-perm (k c) (f c)

caseof-perm : ∀{A B C D E : Set} (k : D → E) {f : C → A ⊎ B} {g : C × A → D} {h : C × B → D}
  → caseof f (k ∘ g) (k ∘ h) ≡ k ∘ caseof f g h
caseof-perm = caseof-perm' ∘ const

caseof-swap : ∀{A B C D X Y : Set}
    (f : C → X ⊎ Y)
    (i : C × X → A ⊎ B)
    (j : C × Y → A ⊎ B)
    (g : C → A → D)
    (h : C → B → D) →
    caseof f (caseof i (uncurry (g ∘ proj₁)) (uncurry (h ∘ proj₁)))
             (caseof j (uncurry (g ∘ proj₁)) (uncurry (h ∘ proj₁)))
      ≡ caseof (caseof f i j) (uncurry g) (uncurry h)
caseof-swap {A} {B} {C} {D} {X} {Y} f i j g h = funExt λ c →
  sum-perm [ (g c) , (h c) ] (f c)
