import Mathlib.Data.Int.Basic
import ClassicalLanguage.State.State

-- logical condition
def Cond := State → Bool

def CondFol(c1: Cond)(c2: Cond):Prop := ∀s:State, c1 s → c2 s

def CondAnd(c1: Cond)(c2: Cond):Cond := (fun s:State => (c1 s) && (c2 s))

def CondNot(c1: Cond):Cond := (fun s:State => ¬(c1 s))
