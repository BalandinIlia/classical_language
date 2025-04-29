import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.de_basic
import ClassicalLanguage.de_BSOS

def hoare(P: Cond)(prog: Program)(Q: Cond): Prop :=
    ∀sStart sFin: State, evalC P sStart → BSOS sStart prog sFin → evalC Q sFin

lemma strengthPostCond (Qn: Cond)(P Q: Cond)(prog: Program):
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

lemma weakenPreCond (Pn: Cond)(P Q: Cond)(prog: Program):
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
  cases trans
  case while_true sInter condVal trans1 trans2 =>
    rw [evalC]
    simp
    apply And.intro
    sorry
    sorry
  case while_false condVal =>
    rw [evalC]
    simp
    apply And.intro
    apply preCond
    rw [evalC]
    simp
    clear preCond hoareBody body Q
    aesop
