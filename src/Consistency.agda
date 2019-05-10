-- Logical consistency of IPL

open import Library

module Consistency (Base : Set) where

import Formulas    ; open module Form = Formulas     Base
import Derivations ; open module Der  = Derivations  Base
import NfModelMonad; open module NfM  = NfModelMonad Base
open Normalization caseTreeMonad using (norm)

-- No variable in the empty context.

noVar : ∀{A} → Hyp A ε → ⊥
noVar ()

-- No neutral in the empty context.

noNe :  ∀{A} → Ne ε A → ⊥
noNe (hyp ())
noNe (impE t u) = noNe t
noNe (andE₁ t)  = noNe t
noNe (andE₂ t)  = noNe t

-- No normal proof of False in the empty context.

noNf : Nf ε False → ⊥
noNf (orE t t₁ t₂) = noNe t
noNf (falseE t)    = noNe t

-- No proof of False in the empty context.

consistency : ε ⊢ False → ⊥
consistency = noNf ∘ norm
