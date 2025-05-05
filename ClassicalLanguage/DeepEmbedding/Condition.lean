import Mathlib.Data.Nat.Basic
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression

inductive Cond
| truee: Cond
| falsee: Cond
| less: Expr → Expr → Cond
| not: Cond → Cond
| and: Cond → Cond → Cond
| or: Cond → Cond → Cond

def evalC: Cond → State → Bool
| Cond.truee, _          =>   true
| Cond.falsee, _         =>   false
| (Cond.less e1 e2), st    =>   (evalE e1 st) < (evalE e2 st)
| (Cond.not c), st       =>   not (evalC c st)
| (Cond.and c1 c2), st   =>   and (evalC c1 st) (evalC c2 st)
| (Cond.or c1 c2), st    =>   or (evalC c1 st) (evalC c2 st)

def replC: Cond → String → Expr → Cond
| Cond.truee, _, _               =>   Cond.truee
| Cond.falsee, _, _              =>   Cond.falsee
| (Cond.less e1 e2), name, eSub  =>   Cond.less (replE e1 name eSub) (replE e2 name eSub)
| (Cond.not c), name, eSub       =>   Cond.not (replC c name eSub)
| (Cond.and c1 c2), name, eSub   =>   Cond.and (replC c1 name eSub) (replC c2 name eSub)
| (Cond.or c1 c2), name, eSub    =>   Cond.or (replC c1 name eSub) (replC c2 name eSub)

lemma condReplacement(cond: Cond)(name: String)(eSub: Expr):
  ∀s:State, (evalC (replC cond name eSub) s) = (evalC cond (replS s name (evalE eSub s))) := by
  intro s
  induction cond with
  | truee =>
    simp [evalC, replC, replE, evalE]
  | falsee =>
    simp [evalC, replC, replE, evalE]
  | less e1 e2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement]
  | not c ih =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih]
  | and c1 c2 ih1 ih2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih1, ih2]

def fol(c1: Cond)(c2: Cond): Prop := ∀s:State, (evalC c1 s) → (evalC c2 s)
