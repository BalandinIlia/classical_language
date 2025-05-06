import Mathlib.Data.Int.Basic
import ClassicalLanguage.State.State
import ClassicalLanguage.ShallowEmbedding.Expression
import ClassicalLanguage.ShallowEmbedding.Condition
import ClassicalLanguage.ShallowEmbedding.Program
import ClassicalLanguage.ShallowEmbedding.BigStepOperationalSemantics
import ClassicalLanguage.ShallowEmbedding.HoareRules

-- expression which increments given variable
def incremExpr(name: String): Expr := Expr.sum (Expr.var name) (Expr.num 1)

-- program which increments given variable
def incremProg(name: String): Program := Program.assign name (incremExpr name)

-- condition that given variable is less then l
def less(name: String)(l: ℤ): Cond := Cond.less (Expr.var name) (Expr.num l)

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

def invar:Cond := Cond.less (Expr.var "j") (Expr.var "i")

theorem example1(decision: Cond)(nIter: ℤ): hoare invar (cycle decision nIter) invar := by
  apply weakenPostCond (Cond.and invar (Cond.not (less "i" nIter)))
  {
    simp [fol, evalC, invar, evalE, less, State]
    intro _
    intro c1
    intro _
    apply c1
  }
  apply hoareWhile

  -- intermediate condition (for seq rule)
  let condInter:Cond := Cond.less (Expr.sum (Expr.var "j") (Expr.num 1)) (Expr.var "i")
  apply hoareSeq invar condInter invar

  {
    apply strengthPreCond (replC condInter "i" (incremExpr "i"))
    simp [replC, condInter, Expr.var, invar, replE, evalC, evalE, fol, incremExpr]
    apply hoareAssign "i" (Expr.sum (Expr.var "i") (Expr.num 1)) condInter
  }
  {
    apply hoareIf
    {
      apply strengthPreCond (replC invar "j" (incremExpr "j"))
      {
        simp [fol, evalC, replC, condInter, evalE, invar, replE, incremExpr]
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
        simp [replC, condInter, Expr.var, invar, replE, evalC, evalE, fol, State]
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
