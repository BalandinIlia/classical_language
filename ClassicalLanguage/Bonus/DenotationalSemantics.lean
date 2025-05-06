import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Aesop
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.Program
import ClassicalLanguage.DeepEmbedding.BigStepOperationalSemantics

open DE

structure Transition where
sSt: State
sFin: State

def DS(prog: Program): Set Transition := {tr: Transition | BSOS tr.sSt prog tr.sFin}

theorem skipRule: DS Program.skip = {tr: Transition | tr.sSt = tr.sFin} := by
  rw [DS]
  have th(s1 s2: State): BSOS s1 Program.skip s2 ↔ s1 = s2 := by
    apply Iff.intro
    {
      intro trans
      cases trans
      simp
    }
    {
      intro eq
      rw [eq]
      apply BSOS.skip
    }
  aesop

theorem assignRule(name: String)(expr: Expr):
  DS (Program.assign name expr) = {tr: Transition | tr.sFin = replS tr.sSt name (evalE expr tr.sSt)} := by
  rw [DS]
  have th(s1 s2: State)(name_: String)(expr_: Expr):
    BSOS s1 (Program.assign name_ expr_) s2 ↔ s2 = replS s1 name_ (evalE expr_ s1) := by
    clear name expr
    apply Iff.intro
    {
      intro trans
      cases trans
      simp
    }
    {
      intro eq
      rw [eq]
      apply BSOS.assign
    }
  aesop

def comp(r1 r2: Set Transition):Set Transition :=
{tr:Transition | ∃s:State, (Transition.mk tr.sSt s) ∈ r1 ∧ (Transition.mk s tr.sFin) ∈ r2}

theorem seqRule(p1 p2: Program):
  DS (Program.seq p1 p2) = comp (DS p1) (DS p2) := by
  simp [DS, comp]
  have eq(s1 s2: State): BSOS s1 (p1.seq p2) s2 ↔ ∃ s, BSOS s1 p1 s ∧ BSOS s p2 s2 := by
    apply Iff.intro
    {
      intro trans
      cases trans
      case seq sInter tr1 tr2 =>
        exists sInter
    }
    {
      intro ex
      let ⟨sInter, prop⟩ := ex
      clear ex
      apply BSOS.seq p1 p2 s1 sInter s2
      aesop
      aesop
    }
  aesop

def filter(set: Set Transition)(fil: Transition → Bool) :=
  {tr:Transition | tr∈set ∧ (fil tr = true)}

theorem ifRule(cond: Cond)(pt pf: Program):
  DS (Program.iff cond pt pf) =
  (filter (DS pt) (fun tr:Transition => (evalC cond tr.sSt) == true))∪
  (filter (DS pf) (fun tr:Transition => (evalC cond tr.sSt) == false)) := by
  simp [DS, filter]
  simp [Set.union_def]
  have eq(s1 s2: State):
    BSOS s1 (Program.iff cond pt pf) s2 ↔
    (BSOS s1 pt s2 ∧ evalC cond s1 = true) ∨ (BSOS s1 pf s2 ∧ evalC cond s1 = false) := by
    apply Iff.intro
    {
      intro trans
      cases trans
      case if_true =>
        aesop
      case if_false =>
        aesop
    }
    {
      intro prop
      apply @Or.elim (BSOS s1 pt s2 ∧ evalC cond s1 = true) (BSOS s1 pf s2 ∧ evalC cond s1 = false)
      apply prop
      {
        clear prop
        intro prop
        apply BSOS.if_true
        aesop
        aesop
      }
      {
        clear prop
        intro prop
        apply BSOS.if_false
        aesop
        aesop
      }
    }
  aesop

def pow: Program → Nat → Set Transition
| _, 0          => DS Program.skip
| p, Nat.succ n => comp (DS p) (pow p n)

theorem whileRule(cond: Cond)(body: Program):
  DS (Program.whilee cond body) = {tr: Transition |
  ¬(evalC cond tr.sFin) ∧ (∃n:ℕ, tr∈(pow body n))} := by
  rw [DS]
  have eq(tr: Transition):
    BSOS tr.sSt (Program.whilee cond body) tr.sFin ↔
    ¬(evalC cond tr.sFin = true) ∧ (∃n:ℕ, tr∈ (pow body n)) := by
    apply Iff.intro
    {
      intro trans
      generalize eq: Program.whilee cond body = prog
      generalize eq1: tr.sSt = s1
      generalize eq2: tr.sFin = s2
      rw [eq, eq1, eq2] at trans
      rw [Eq.comm] at eq
      revert eq2 eq eq1 tr cond body
      induction trans with
      | while_true iCond iBody s3 s4 s5 condVal tr1 tr2 ih1 ih2 =>
        intro cond body tr eq eq1 eq2
        simp at eq
        simp [eq] at condVal ih1 ih2 tr1 tr2
        simp
        apply And.intro
        {
          apply And.left
          apply ih2 cond body (Transition.mk s4 s5)
          simp
          simp
          simp
          simp
        }
        {
          have tmp: ∃ n, (Transition.mk s4 s5) ∈ pow body n := by
            aesop
          let ⟨nn, prop⟩ := tmp
          exists nn+1
          clear eq ih1 tmp tr2 ih2 condVal iCond iBody s1 s2
          rw [pow]
          simp [comp]
          exists s4
          apply And.intro
          simp [eq1]
          rw [DS]
          aesop
          rw [eq2]
          apply prop
        }
      | while_false iCond iBody ss condVal =>
        intro cond body tr eq eq1 eq2
        simp at eq
        simp [eq] at condVal
        simp
        apply And.intro
        apply condVal
        exists 0
        simp [pow]
        rw [skipRule]
        aesop
      | seq =>
        intro cond body tr eq eq1 eq2
        aesop
      | skip =>
        intro cond body tr eq eq1 eq2
        aesop
      | assign =>
        intro cond body tr eq eq1 eq2
        aesop
      | if_true =>
        intro cond body tr eq eq1 eq2
        aesop
      | if_false =>
        intro cond body tr eq eq1 eq2
        aesop
    }
    {
      sorry
    }
  simp [eq]

def examp1:Program :=
Program.iff (Cond.less (Expr.var "a") (Expr.num 0))
            (Program.assign "b" (Expr.num (-1)))
            (Program.assign "b" (Expr.num 1))

def examp2:Program :=
Program.iff (Cond.not (Cond.less (Expr.var "a") (Expr.num 0)))
            (Program.assign "b" (Expr.num 1))
            (Program.assign "b" (Expr.num (-1)))

theorem th: DS examp1 = DS examp2 := by
  simp [examp1, examp2]
  rw [ifRule]
  rw [ifRule]
  rw [filter]
  rw [filter]
  rw [filter]
  rw [filter]
  rw [assignRule]
  rw [assignRule]
  simp [replS, evalC, evalE, State, Transition, Set.union_def]
  aesop
