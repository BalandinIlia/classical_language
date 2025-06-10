# classical_language
This repository is a formalization of a simple imperative WHILE language, which contains integer variables, arithmetic expressions, if and while constructs.

It has the following folders:
1) State: contains one file which formalizes state of the memory.
2) ShallowEmbedding: contains formalization of language with shallow embedding of expressions and conditions:
2.1) Condition and Expression files formalize conditions and expressions correspondingly.
2.2) Program formalizes language syntax
2.3) BigStepOperationalSemantics formalizes big-step-operational semantic.
2.4) HoareRules formalize correct Hoare triple definition and formalize and prove Hoare rules basing on big-step-operational semantics.
2.5) HoareLogicExample presents a sample program and hoare triple proven for this program.
3) DeepEmbedding: contains formalization of language with deep embedding of expressions and conditions. Files and their purposes are analogous to ShallowEmbedding folder.
4) Bonus: contains some additional (optional) developments for the language.