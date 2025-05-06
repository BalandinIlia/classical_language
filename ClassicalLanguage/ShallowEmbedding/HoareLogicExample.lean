import Mathlib.Data.Int.Basic
import ClassicalLanguage.State.State
import ClassicalLanguage.ShallowEmbedding.Expression
import ClassicalLanguage.ShallowEmbedding.Condition
import ClassicalLanguage.ShallowEmbedding.Program
import ClassicalLanguage.ShallowEmbedding.BigStepOperationalSemantics
import ClassicalLanguage.ShallowEmbedding.HoareRules

namespace SE

-- expression which calculates given variable incremented
def incremExpr(name: String): Expr := (fun st:State => st name + 1)

-- program which increments given variable
def incremProg(name: String): Program := Program.assign name (incremExpr name)

-- condition that given variable is less then l
def less(name: String)(l: ℤ): Cond := (fun st:State => st name < l)

def cycle(decision: Cond)(nIter: ℤ): Program :=
Program.whilee (less "i" nIter)
               (Program.seq
                          (incremProg "i")
                          (Program.iff
                                      decision
                                      (incremProg "j")
                                      Program.skip
                          )
               )

def invar:Cond := (fun st:State => st "j" < st "i")

theorem example1(decision: Cond)(nIter: ℤ): hoare invar (cycle decision nIter) invar := by
  apply weakenPostCond (CondAnd invar (CondNot (less "i" nIter)))
  {
    simp [CondFol, CondAnd, CondNot, less, invar]
    intro _
    intro c1
    intro _
    apply c1
  }
  apply hoareWhile

  -- intermediate condition (for seq rule)
  let condInter:Cond := (fun st:State => st "j" + 1 < st "i")
  apply hoareSeq invar condInter invar

  {
    apply strengthPreCond (fun st:State => condInter (replS st "i" (incremExpr "i" st)))
    simp [CondFol, condInter, replS, incremExpr, invar]
    apply hoareAssign "i" (incremExpr "i") condInter
  }
  {
    apply hoareIf
    {
      apply strengthPreCond (fun st:State => invar (replS st "j" (incremExpr "j" st)))
      {
        simp [CondFol, CondAnd, condInter, incremExpr, replS, invar]
        clear nIter condInter
        intro _
        intro c
        intro _
        apply c
      }
      {
        clear condInter decision
        apply hoareAssign
      }
    }
    {
      apply strengthPreCond invar
      {
        simp [CondFol, CondAnd, condInter, CondNot, invar, State]
        clear nIter condInter
        intro s
        intro c
        intro t
        clear t decision
        generalize A: s "i" = a
        generalize B: s "j" = b
        simp [A, B] at c
        clear s A B
        apply @Int.lt_trans b (b + 1) a
        apply @Int.lt_add_succ b 0
        apply c
      }
      apply hoareSkip invar
    }
  }
