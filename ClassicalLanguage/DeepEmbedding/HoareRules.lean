import Mathlib.Data.Int.Basic
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.Program
import ClassicalLanguage.DeepEmbedding.BigStepOperationalSemantics

namespace DE

-- Definition of correct Hoare triple
def hoare(P: Cond)(prog: Program)(Q: Cond): Prop :=
    ∀sStart sFin: State, evalC P sStart → BSOS sStart prog sFin → evalC Q sFin

-- This lemma allows to get one correct hoare triple from another by weakening postcondition
lemma weakenPostCond (Q: Cond)(Qn: Cond)(P: Cond)(prog: Program):
  fol Q Qn → hoare P prog Q → hoare P prog Qn := by
  intro weaker
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
  apply weaker sFin
  apply postCond

-- This lemma allows to get one correct hoare triple from another by strengthening precondition
lemma strengthPreCond (P: Cond)(Pn: Cond)(Q: Cond)(prog: Program):
    fol Pn P → hoare P prog Q → hoare Pn prog Q := by
    intro stronger
    intro hoare1
    rw [hoare]
    intro sStart sFin
    intro preCond
    intro trans
    apply hoare1 sStart sFin
    apply stronger sStart
    apply preCond
    apply trans

-- hoare rule for skip construction
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

-- hoare rule for assign
theorem hoareAssign(name: String)(expr: Expr)(Q: Cond):
  hoare (replC Q name expr) (Program.assign name expr) Q := by
  rw [hoare]
  intro sStart sFin
  intro precond
  intro trans
  rw [condReplacement] at precond
  cases trans
  case assign =>
    apply precond

-- hoare rule for sequence
theorem hoareSeq(P R Q: Cond)(p1 p2: Program):
  hoare P p1 R →
  hoare R p2 Q →
  hoare P (Program.seq p1 p2) Q := by
  intro hoare1
  intro hoare2

  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans

  cases trans
  case seq sInter trans1 trans2 =>
    apply hoare2 sInter sFin
    apply hoare1 sStart sInter
    apply preCond
    apply trans1
    apply trans2

-- hoare rule for if
-- pt = "program true", - program which executes if condition is true
-- pf = "program false", - program which executes if condition is false
theorem hoareIf(P Q: Cond)(cond: Cond)(pt pf: Program):
  hoare (Cond.and P cond) pt Q →
  hoare (Cond.and P (Cond.not cond)) pf Q →
  hoare P (Program.iff cond pt pf) Q := by
  intro hoareT
  intro hoareF
  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans
  cases trans
  case if_true condVal transt =>
    clear hoareF pf
    apply hoareT sStart sFin
    {
      simp [evalC]
      apply And.intro
      apply preCond
      apply condVal
    }
    apply transt
  case if_false condVal transf =>
    clear hoareT pt
    apply hoareF sStart sFin
    {
      simp [evalC]
      apply And.intro
      apply preCond
      simp at condVal
      apply condVal
    }
    apply transf

-- Lemma that cycle invariant is preserved in cycle if it is preserved in cycle body
lemma transInv(prog: Program)(Q: Cond)
  (decom: ∃c:Cond, ∃b:Program, prog = Program.whilee c b ∧ hoare Q b Q):
  hoare Q prog Q := by
  rw[hoare]
  intro sStart sFin
  intro pre
  intro trans
  revert pre
  revert decom
  revert Q

  induction trans with
  | while_true cond body s1 s2 s3 valCond tr1 tr2 ih1 ih2 =>
    intro Q
    clear prog
    clear sStart sFin
    clear ih1 tr2

    intro decom
    let ⟨c, b, hoareBody⟩ := decom
    simp at hoareBody
    have eq1: c = cond := by
      rw [Eq.comm]
      apply @And.left (cond = c) (body = b)
      apply @And.left (cond = c ∧ body = b) (hoare Q b Q)
      apply hoareBody
    have eq2: b = body := by
      rw [Eq.comm]
      apply @And.right (cond = c) (body = b)
      apply @And.left (cond = c ∧ body = b) (hoare Q b Q)
      apply hoareBody
    rw [eq1, eq2] at hoareBody
    simp at hoareBody
    clear c b eq1 eq2

    intro preCond
    apply ih2
    apply decom
    apply hoareBody s1 s2
    apply preCond
    apply tr1
  | while_false =>
    simp
  | skip _ =>
    clear prog sStart sFin
    intro Q
    intro decom
    apply False.elim
    let ⟨c, b, prop⟩ := decom
    clear decom
    nomatch prop
  | assign _ _ _ =>
    clear prog sStart sFin
    intro Q
    intro decom
    apply False.elim
    let ⟨c, b, prop⟩ := decom
    clear decom
    nomatch prop
  | seq =>
    clear prog sStart sFin
    intro Q
    intro decom
    apply False.elim
    let ⟨c, b, prop⟩ := decom
    clear decom
    nomatch prop
  | if_true =>
    clear prog sStart sFin
    intro Q
    intro decom
    apply False.elim
    let ⟨c, b, prop⟩ := decom
    clear decom
    nomatch prop
  | if_false =>
    clear prog sStart sFin
    intro Q
    intro decom
    apply False.elim
    let ⟨c, b, prop⟩ := decom
    clear decom
    nomatch prop

theorem hoareWhile(Q: Cond)(cond: Cond)(body: Program):
  hoare Q body Q → hoare Q (Program.whilee cond body) (Cond.and Q (Cond.not cond)) := by
  intro hoareBody
  rw [hoare]
  intro sStart sFin
  intro preCond
  intro trans
  simp [evalC]
  apply And.intro
  {
    apply transInv (Program.whilee cond body) Q _ sStart sFin
    apply preCond
    apply trans
    exists cond
    exists body
  }
  {
    clear Q hoareBody preCond
    generalize progEq: (Program.whilee cond body) = prog
    rw [progEq] at trans
    rw [Eq.comm] at progEq
    revert progEq
    revert cond body
    induction trans with
    | while_true cond body s1 s2 s3 condVal tr1 tr2 ih1 ih2 =>
      clear sStart sFin tr1 ih1
      intro c b
      intro eq
      simp at eq
      apply ih2 c b
      simp
      apply eq
    | while_false cond body s condVal =>
      clear sStart sFin prog
      simp at condVal
      intro c b
      intro eq
      simp at eq
      have eq2: c=cond := by
        clear s condVal
        rw [Eq.comm]
        apply And.left
        apply eq
      rw [eq2]
      apply condVal
    | skip =>
      intro c b st
      clear sStart sFin prog
      apply False.elim
      nomatch st
    | assign =>
      intro c b st
      apply False.elim
      nomatch st
    | seq =>
      intro c b st
      apply False.elim
      nomatch st
    | if_true =>
      intro c b st
      apply False.elim
      nomatch st
    | if_false =>
      intro c b st
      apply False.elim
      nomatch st
  }
