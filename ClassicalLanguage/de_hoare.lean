import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.de_basic
import ClassicalLanguage.de_BSOS

def hoare(P: Cond)(prog: Program)(Q: Cond): Prop :=
    ∀sStart sFin: State, evalC P sStart → BSOS sStart prog sFin → evalC Q sFin

lemma strnegthPostCond (Q: Cond)(Qn: Cond)(P: Cond)(prog: Program):
    fol Q Qn → hoare P prog Q → hoare P prog Qn := by
  intro stronger
  intro hoare1
  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans
  have postCond: evalC Q sFin := by
    apply hoare1 sStart sFin
    apply preCond
    apply trans
  clear preCond trans sStart hoare1 prog P
  apply stronger sFin
  apply postCond

lemma weakenPreCond (P: Cond)(Pn: Cond)(Q: Cond)(prog: Program):
    fol Pn P → hoare P prog Q → hoare Pn prog Q := by
    intro weaker
    intro hoare1
    rw [hoare]
    intro sStart sFin
    intro preCond
    intro trans
    apply hoare1 sStart sFin
    apply weaker sStart
    apply preCond
    apply trans

theorem hoareSkip(P: Cond): hoare P Program.skip P := by
  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans
  have eq: sFin = sStart := by
    cases trans
    simp
  simp [eq]
  apply preCond

theorem hoareAssign(name: String)(expr: Expr)(Q: Cond):
  hoare (replC Q name expr) (Program.assign name expr) Q := by
  rw [hoare]
  intro sStart sFin
  rw [condReplacement]
  intro precond
  intro trans
  cases trans
  case assign =>
    apply precond

theorem hoareSeq(P R Q: Cond)(p1 p2: Program):
  ((hoare P p1 R) → (hoare R p2 Q) → (hoare P (Program.seq p1 p2) Q)) := by
  intro hoare1
  intro hoare2

  rw [hoare]
  intro sStart
  intro sFin
  intro preCond
  intro trans

  cases trans
  case seq sInter trans1 trans2 =>
    apply hoare2 sInter sFin
    apply hoare1 sStart sInter
    apply preCond
    apply trans1
    apply trans2

theorem hoareIf(P Q: Cond)(cond: Cond)(pt pf: Program):
  hoare P pt Q → hoare P pf Q → hoare P (Program.iff cond pt pf) Q := by
  intro hoaret
  intro hoaref
  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans
  cases trans
  case if_true condVal transt =>
    apply hoaret sStart
    apply preCond
    apply transt
  case if_false condVal transf =>
    apply hoaref sStart
    apply preCond
    apply transf

theorem hoareWhile(Q: Cond)(cond: Cond)(body: Program):
  hoare Q body Q → hoare Q (Program.whilee cond body) (Cond.and Q (Cond.not cond)) := by
  intro hoareBody
  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans
  generalize hprog: (Program.whilee cond body) = prog
  rw [hprog] at trans
  rw [evalC]
  simp
  apply And.intro
  {
    have df: (prog = Program.whilee cond body) → (hoare Q body Q) → (evalC Q sStart = true) → (evalC Q sFin = true) := by
      induction trans with
      | while_true iCond iBody s1 s2 s3 valICond tr1 tr2 ih1 ih2 =>
        intro h1 h2 h3
        rw [h1] at hprog
        have eq: body = iBody := by
          aesop
        apply ih2
        apply hoareBody
        apply h3
        rw [eq]
        apply tr1
        rw [Eq.comm]
        apply h1
        apply h1
        apply hoareBody
        apply hoareBody s1 s2
        apply preCond
        have eq2: iBody = body := by
          rw [Eq.comm]
          apply eq
        rw [eq]
        apply tr1
      | while_false iCond iBody s1 s2 =>
        intro h1 h2 h3
        apply h3
      | skip =>
        aesop
      | assign =>
        aesop
      | seq p1 p2 s1 s2 s3 tr1 tr2 ih1 ih2 =>
        apply False.elim
        aesop
      | if_true =>
        apply False.elim
        aesop
      | if_false =>
        apply False.elim
        aesop
    apply df
    rw [Eq.comm]
    apply hprog
    apply hoareBody
    apply preCond
  }
  {
    rw [evalC]
    simp
    induction trans with
    | while_true =>
      aesop
    | while_false =>
      aesop
    | skip =>
      aesop
    | assign =>
      aesop
    | seq =>
      aesop
    | if_true =>
      aesop
    | if_false =>
      aesop
  }

-- Example

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
