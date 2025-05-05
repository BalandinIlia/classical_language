import Mathlib.Data.Nat.Basic
import Aesop
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
      aesop
    case false =>
      have neq:¬(name2 = name) := by
        aesop
      simp [neq]
      simp [evalE]
  | sum e1 e2 ih1 ih2 =>
    simp [evalE, replE, replS, ih1, ih2]
  | dif e1 e2 ih1 ih2 =>
    simp [evalE, replE, replS, ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    simp [evalE, replE, replS, ih1, ih2]

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

inductive Program
| skip: Program
| assign: String → Expr → Program
| seq: Program → Program → Program
| iff: Cond → Program → Program → Program
| whilee: Cond → Program → Program
