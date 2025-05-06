-- This module serves as the root of the `ClassicalLanguage` library.
-- Import modules here that should be built as part of the library.

import ClassicalLanguage.State.State

import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.Program
import ClassicalLanguage.DeepEmbedding.BigStepOperationalSemantics
import ClassicalLanguage.DeepEmbedding.HoareRules
import ClassicalLanguage.DeepEmbedding.HoareLogicExample

import ClassicalLanguage.ShallowEmbedding.first

import ClassicalLanguage.Bonus.de_SSOS
import ClassicalLanguage.Bonus.de_SSOS_alternative
import ClassicalLanguage.Bonus.de_unlooping
import ClassicalLanguage.Bonus.de_termination_determenism

import Mathlib
