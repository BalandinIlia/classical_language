import Mathlib.Data.Nat.Basic
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression

-- logical condition
inductive Cond
| truee: Cond
| falsee: Cond
| less: Expr → Expr → Cond
| not: Cond → Cond
| and: Cond → Cond → Cond
| or: Cond → Cond → Cond

-- evaluate given condition according to given state
def evalC: Cond → State → Bool
| Cond.truee, _          =>   true
| Cond.falsee, _         =>   false
| (Cond.less e1 e2), st  =>   (evalE e1 st) < (evalE e2 st)
| (Cond.not c), st       =>   not (evalC c st)
| (Cond.and c1 c2), st   =>   and (evalC c1 st) (evalC c2 st)
| (Cond.or c1 c2), st    =>   or (evalC c1 st) (evalC c2 st)

-- replace given variable with given expression inside given condition
def replC: Cond → String → Expr → Cond
| Cond.truee, _, _               =>   Cond.truee
| Cond.falsee, _, _              =>   Cond.falsee
| (Cond.less e1 e2), name, eSub  =>   Cond.less (replE e1 name eSub) (replE e2 name eSub)
| (Cond.not c), name, eSub       =>   Cond.not (replC c name eSub)
| (Cond.and c1 c2), name, eSub   =>   Cond.and (replC c1 name eSub) (replC c2 name eSub)
| (Cond.or c1 c2), name, eSub    =>   Cond.or (replC c1 name eSub) (replC c2 name eSub)

-- replacement of variable in condition is the same as replacement in state
lemma condReplacement(cond: Cond)(name: String)(eSub: Expr):
  ∀s:State, (evalC (replC cond name eSub) s) = (evalC cond (replS s name (evalE eSub s))) := by
  intro s
  induction cond with
  | truee =>
    simp [evalC, replC, replE, evalE]
  | falsee =>
    simp [evalC, replC, replE, evalE]
  | less _ _ =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement]
  | not _ ih =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih]
  | and _ _ ih1 ih2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih1, ih2]
  | or _ _ ih1 ih2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih1, ih2]

-- one condtion follows from another
def fol(c1: Cond)(c2: Cond): Prop := ∀s:State, (evalC c1 s) → (evalC c2 s)
