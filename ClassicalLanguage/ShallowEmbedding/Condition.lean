import Mathlib.Data.Int.Basic
import ClassicalLanguage.State.State

-- logical condition
def Cond := State → Bool

def fol(c1: Cond)(c2: Cond) := ∀s:State, c1 s → c2 s
