import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.Program
import ClassicalLanguage.DeepEmbedding.BigStepOperationalSemantics
import ClassicalLanguage.DeepEmbedding.HoareRules

def increm(name: String): Program := Program.assign name (Expr.sum (Expr.var name) (Expr.num 1))

def decision(name: String): Cond := Cond.less (Expr.var name) (Expr.num 50)

def less100(name: String): Cond := Cond.less (Expr.var name) (Expr.num 100)

def cycle: Program :=
Program.whilee (less100 "i")
               (Program.seq
                          (increm "i")
                          (Program.iff
                                      (decision "i")
                                      (increm "j")
                                      Program.skip
                          )

               )

def invar:Cond := Cond.less (Expr.var "j") (Expr.var "i")

theorem example1: hoare invar cycle invar := by
  apply strnegthPostCond (Cond.and invar (Cond.not (less100 "i")))
  {
    simp [fol, evalC, invar, evalE, less100, State]
    aesop
  }
  apply hoareWhile

  let condInter:Cond := Cond.less (Expr.sum (Expr.var "j") (Expr.num 1)) (Expr.var "i")

  apply hoareSeq invar condInter invar
  {
    apply weakenPreCond (replC condInter "i" (Expr.sum (Expr.var "i") (Expr.num 1)))
    simp [replC, condInter, Expr.var, invar, replE, evalC, evalE, fol]
    apply hoareAssign "i" (Expr.sum (Expr.var "i") (Expr.num 1)) condInter
  }
  {
    apply hoareIf
    {
      apply weakenPreCond (replC invar "j" (Expr.sum (Expr.var "j") (Expr.num 1)))
      simp [fol, evalC, replC, condInter, evalE, invar, replE]
      apply hoareAssign
    }
    {
      apply weakenPreCond invar
      simp [replC, condInter, Expr.var, invar, replE, evalC, evalE, fol, State]
      clear condInter
      {
        intro s
        intro neq
        apply @Int.lt_trans (s "j") (s "j" + 1) (s "i")
        apply Int.lt_add_of_pos_right
        simp
        apply neq
      }
      apply hoareSkip
    }
  }
