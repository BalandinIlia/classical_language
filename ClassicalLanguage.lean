-- This module serves as the root of the `ClassicalLanguage` library.
-- Import modules here that should be built as part of the library.

import ClassicalLanguage.State.State

import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.Program
import ClassicalLanguage.DeepEmbedding.BigStepOperationalSemantics
import ClassicalLanguage.DeepEmbedding.HoareRules
import ClassicalLanguage.DeepEmbedding.HoareLogicExample

import ClassicalLanguage.ShallowEmbedding.Expression
import ClassicalLanguage.ShallowEmbedding.Condition
import ClassicalLanguage.ShallowEmbedding.Program
import ClassicalLanguage.ShallowEmbedding.BigStepOperationalSemantics
import ClassicalLanguage.ShallowEmbedding.HoareRules
import ClassicalLanguage.ShallowEmbedding.HoareLogicExample

import ClassicalLanguage.Bonus.SmallStepSemantics
import ClassicalLanguage.Bonus.SmallStepSemanticsAlternative
import ClassicalLanguage.Bonus.TerminationDetermenizm

import Mathlib
