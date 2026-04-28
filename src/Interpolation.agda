
open import Library

module Interpolation (Base : Set) where

open import Formulas Base
open import Derivations Base

Voc = Base → Set

_⊂_ : (L M : Voc) → Set
L ⊂ M = ∀{P : Base} → L P → M P

variable
   P : Base
   A B C : Form
   Γ Δ : Cxt
   x   : Hyp A Γ
   u   : Ne Γ A
   v   : Nf Γ A
   L M : Voc

data _∋_ (L : Voc) : (A : Form) → Set where
  Atom  : (p : L P) → L ∋ Atom P
  True  : L ∋ True
  False : L ∋ False
  _∧_   : (pA : L ∋ A) (pB : L ∋ B) → L ∋ (A ∧ B)
  _∨_   : (pA : L ∋ A) (pB : L ∋ B) → L ∋ (A ∨ B)
  _⇒_   : (pA : L ∋ A) (pB : L ∋ B) → L ∋ (A ⇒ B)

monL : (t : L ⊂ M) → L ∋ A → M ∋ A
monL t (Atom p) = Atom (t p)
monL t True = True
monL t False = False
monL t (p ∧ p₁) = monL t p ∧ monL t p₁
monL t (p ∨ p₁) = monL t p ∨ monL t p₁
monL t (p ⇒ p₁) = monL t p ⇒ monL t p₁

data Color : Set where
  white red blue : Color

op : Color → Color
op white = white
op red = blue
op blue = red

variable
  c c' c'' ca : Color

data _≺_ : (c c' : Color) → Set where
  white : ∀{c} → white ≺ c
  red   : red ≺ red
  blue  : blue ≺ blue

_≺trans_ : c ≺ c' → c' ≺ c'' → c ≺ c''
white ≺trans q    = white
red   ≺trans red  = red
blue  ≺trans blue = blue

-- Color assignment

module _ (color : Base → Color) where

  -- Colored atom
  -- data CA (c : Color) (P : Base) : Set where
  --   ca : color P ≺ c

  CA : (c : Color) (P : Base) → Set
  CA c P = color P ≺ c

  -- Colored formula
  CF : Color → Form → Set
  CF c A = CA c ∋ A

  monC : (c≺c' : c ≺ c') → CF c A → CF c' A
  monC c≺c' = monL (_≺trans c≺c')

  data CC : (Γ : Cxt) → Set where
    ε     : CC ε
    _∙_∶_ : (G : CC Γ) (c : Color) (H : CF c A) → CC (Γ ∙ A)

  variable
    R : CA c P
    H HA HB HC : CF c A
    G : CC Γ

  data CHyp (c : Color) : (G : CC Γ) (x : Hyp A Γ) → Set where
    top : (le : ca ≺ c) → CHyp c (G ∙ ca ∶ H) top
    pop : CHyp c G x → CHyp c (G ∙ ca ∶ H) (pop x)

  mutual
    data CNe (G : CC Γ) (c : Color) (H : CF c A) : (u : Ne Γ A) → Set where
      hyp  : (X : CHyp c G x) → CNe G c H (hyp x)
      impE : (U : CNe G c (H ⇒ HB) u) (V : CNf G c HB v) → CNe G c H (impE u v)

    data CNf (G : CC Γ) (c : Color) : (H : CF c A) (v : Nf Γ A) → Set where
      ne   : (U : CNe G c (Atom R) u) → CNf G c (Atom R) (ne u)
      impI : (V : CNf (G ∙ c ∶ HA) c HB v) → CNf G c (HA ⇒ HB) (impI v)

  data InterpolNe (G : CC Γ) (t : Ne Γ C) : Set where
    ne : (HB : CF white B) (c : Color) (HC : CF c C)
     (U : CNf (G ∙ white ∶ HB) c HC v)
     (V : CNe G (op c) HB u)
     → InterpolNe G t

  data InterpolNf (G : CC Γ) (c : Color) (H : CF c C) (t : Nf Γ C) : Set where
    nf : (HB : CF white B)
     (U : CNf (G ∙ white ∶ B) c HC v)
     (V : CNe G (op c) HB u)
     → InterpolNe G c H t

-- -}
-- -}
-- -}
-- -}
-- -}
