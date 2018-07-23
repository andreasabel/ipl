-- Normalization by Evaluation for Intuitionistic Predicate Logic (IPL)

module Everything where

-- Imports from the standard library and simple definitions

import Library

-- Types and terms of IPL

import Formulas
import Derivations

-- Beth model

import TermModel
import NfModel

-- A variant where Cover : PSh → PSh

import NfModelCaseTree        -- Presented at ITC 2018-07-19
import NfModelCaseTreeConv

-- A generalization to any CoverMonad which includes the
-- continuation monad used in Danvy's algorithm

import NfModelMonad

-- A monadic interpreter using shift/reset and an optimization

import DanvyShiftReset
import DanvyShiftResetLiftable

-- SET-interpretation and soundness of NbE

import Interpretation
import NbeModel

-- A general theory of sheaves over preorders

import PresheavesAndSheaves
