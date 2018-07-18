-- Normalization for Intuitionistic Predicate Logic (IPL)

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

import NfModelCaseTree
import NfModelCaseTreeConv

-- SET-interpretation and soundness of NbE

import Interpretation
import NbeModel

-- A monadic interpreter using shift/reset and an optimization

import DanvyShiftReset
import DanvyShiftResetLiftable

-- A general theory of sheaves over preorders

import PresheavesAndSheaves
