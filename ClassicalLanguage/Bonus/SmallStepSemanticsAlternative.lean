import Mathlib.Data.Int.Basic
import Aesop
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.BigStepOperationalSemantics

open DE

-- execu means execution:
-- program 2 can be got from program 1 in one small execution step
inductive execu: Program → Program → Prop
| assign(n: String)(expr: Expr):
    execu (Program.assign n expr) Program.skip
| if_true(c:Cond)(pt pf: Program):
    execu (Program.iff c pt pf) pt
| if_false(c:Cond)(pt pf: Program):
    execu (Program.iff c pt pf) pf
| seqSkip(p: Program):
    execu (Program.seq Program.skip p) p
| seq(p1s p1f p2: Program):
    execu p1s p1f →
    execu (Program.seq p1s p2) (Program.seq p1f p2)
| while_true(c: Cond)(b: Program):
    execu (Program.whilee c b) (Program.seq b (Program.whilee c b))
| while_false(c: Cond)(b: Program):
    execu (Program.whilee c b) Program.skip

-- true if state1 program1 can be transformed to state2 program2
def aSSOS(state1: State)(program1: Program)
         (state2: State)(program2: Program): Prop :=
         (∀sFin:State, BSOS state1 program1 sFin ↔ BSOS state2 program2 sFin) ∧
         (execu program1 program2)

theorem aSSOS_assign (st: State)(name: String)(expr: Expr):
  aSSOS st (Program.assign name expr) (replS st name (evalE expr st)) Program.skip := by
  rw [aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro bsos1
      cases bsos1
      apply BSOS.skip
    }
    {
      intro bsos1
      cases bsos1
      apply BSOS.assign
    }
  }
  apply execu.assign

theorem aSSOS_seq (st1 st2: State)(p1s p1f p2: Program):
  aSSOS st1 p1s st2 p1f →
  aSSOS st1 (Program.seq p1s p2) st2 (Program.seq p1f p2) := by
  rw [aSSOS]
  simp
  intro trans
  intro ss
  rw [aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro bsos1
      cases bsos1
      case seq sInter tr1s tr2 =>
      apply BSOS.seq p1f p2 st2 sInter
      {
        have tmp := trans sInter
        rw [Iff.comm] at tmp
        rw [tmp]
        apply tr1s
      }
      apply tr2
    }
    {
      intro bsos1
      cases bsos1
      case seq sInter tr1s tr2 =>
      apply BSOS.seq p1s p2 st1 sInter
      {
        have tmp := trans sInter
        rw [tmp]
        apply tr1s
      }
      apply tr2
    }
  }
  apply execu.seq
  apply ss

theorem aSSOS_seq_skip (st: State)(prog: Program):
  aSSOS st (Program.seq Program.skip prog) st prog := by
  rw [aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro bsos1
      cases bsos1
      case seq sInter tr1 tr2 =>
      cases tr1
      apply tr2
    }
    {
      intro bsos1
      apply BSOS.seq Program.skip prog st st
      apply BSOS.skip
      apply bsos1
    }
  }
  apply execu.seqSkip

theorem aSSOS_if_true (st: State)(cond: Cond)(pt pf: Program):
  evalC cond st = true →
  aSSOS st (Program.iff cond pt pf) st pt := by
  intro condVal
  rw [aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro bsos1
      cases bsos1
      case if_true _ d =>
        apply d
      case if_false =>
        apply False.elim
        aesop
    }
    {
      intro bsos1
      apply BSOS.if_true
      apply condVal
      apply bsos1
    }
  }
  apply execu.if_true

theorem aSSOS_if_false (st: State)(cond: Cond)(pt pf: Program):
  evalC cond st = false →
  aSSOS st (Program.iff cond pt pf) st pf := by
  intro condVal
  rw [aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro bsos1
      cases bsos1
      case if_false _ f =>
        apply f
      case if_true _ _ =>
        apply False.elim
        aesop
    }
    {
      intro bsos1
      apply BSOS.if_false
      simp
      apply condVal
      apply bsos1
    }
  }
  apply execu.if_false

theorem aSSOS_while_true (st: State)(cond: Cond)(body: Program):
  evalC cond st = true →
  aSSOS st (Program.whilee cond body) st (Program.seq body (Program.whilee cond body)) := by
  intro condVal
  rw[aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro trans
      cases trans
      case while_true sInter tmp tr1 tr2 =>
        apply BSOS.seq body (Program.whilee cond body) st sInter
        apply tr1
        apply tr2
      case while_false =>
        apply False.elim
        aesop
    }
    {
      intro trans
      cases trans
      case seq sInter tr1 tr2 =>
        apply BSOS.while_true cond body st sInter sFin
        apply condVal
        apply tr1
        apply tr2
    }
  }
  apply execu.while_true

theorem aSSOS_while_false (st: State)(cond: Cond)(body: Program):
  evalC cond st = false →
  aSSOS st (Program.whilee cond body) st Program.skip := by
  intro condVal
  rw[aSSOS]
  apply And.intro
  {
    intro sFin
    apply Iff.intro
    {
      intro trans
      cases trans
      case while_true sInter tmp tr1 tr2 =>
        apply False.elim
        aesop
      case while_false =>
        apply BSOS.skip
    }
    {
      intro trans
      cases trans
      apply BSOS.while_false cond body st
      simp
      apply condVal
    }
  }
  apply execu.while_false

-- pair state-program is final
def final(_: State)(program: Program): Prop := program = Program.skip

-- pair state-program is blocked, - it allows no further transition
def blocked(state: State)(program: Program): Prop :=
  ¬(∃s2:State, ∃p2:Program, aSSOS state program s2 p2)

def blockedFinal:Prop :=
∀st: State,
∀prog: Program,
(final st prog) ↔ (blocked st prog)

def determ:Prop :=
∀st1 st2 st3: State,
∀prog1 prog2 prog3: Program,
aSSOS st1 prog1 st2 prog2 →
aSSOS st1 prog1 st3 prog3 →
((st2 = st3) ∧ (prog2 = prog3))
