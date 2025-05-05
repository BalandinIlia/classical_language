import Mathlib.Data.Nat.Basic
import ClassicalLanguage.State.State

inductive Expr
| num: ℤ → Expr
| var: String → Expr
| sum: Expr → Expr → Expr
| dif: Expr → Expr → Expr
| mul: Expr → Expr → Expr

def evalE: Expr → State → ℤ
| (Expr.num n), _        =>   n
| (Expr.var s), st       =>   st s
| (Expr.sum e1 e2), st   =>   (evalE e1 st) + (evalE e2 st)
| (Expr.dif e1 e2), st   =>   (evalE e1 st) - (evalE e2 st)
| (Expr.mul e1 e2), st   =>   (evalE e1 st) * (evalE e2 st)

def replE: Expr → String → Expr → Expr
| (Expr.num n), _, _             =>   Expr.num n
| (Expr.var s), name, eSub       =>   if (s==name) then eSub else (Expr.var s)
| (Expr.sum e1 e2), name, eSub   =>   Expr.sum (replE e1 name eSub) (replE e2 name eSub)
| (Expr.dif e1 e2), name, eSub   =>   Expr.dif (replE e1 name eSub) (replE e2 name eSub)
| (Expr.mul e1 e2), name, eSub   =>   Expr.mul (replE e1 name eSub) (replE e2 name eSub)

lemma exprReplacement(expr: Expr)(name: String)(eSub: Expr):
  ∀s:State, (evalE (replE expr name eSub) s) = (evalE expr (replS s name (evalE eSub s))) := by
  intro s
  induction expr with
  | num =>
    simp [evalE, replE, replS]
  | var name2 =>
    simp [evalE, replE, replS]
    cases eq : (name2==name)
    case true =>
      simp at eq
      simp [eq]
    case false =>
      simp at eq
      simp [eq, evalE]
  | sum e1 e2 ih1 ih2 =>
    simp [evalE, replE, replS, ih1, ih2]
  | dif e1 e2 ih1 ih2 =>
    simp [evalE, replE, replS, ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    simp [evalE, replE, replS, ih1, ih2]
