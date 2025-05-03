import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.de_basic
import ClassicalLanguage.de_BSOS

-- SS means small step: program 2 can be got from program 1 in one small step
inductive SS: Program → Program → Prop
| assign(n: String)(expr: Expr): SS (Program.assign n expr) Program.skip
| if_true(c:Cond)(pt pf: Program): SS (Program.iff c pt pf) pt
| if_false(c:Cond)(pt pf: Program): SS (Program.iff c pt pf) pf
| seqSkip(p: Program): SS (Program.seq Program.skip p) p
| seq(p1s p1f p2: Program): SS (Program.seq p1s p2) (Program.seq p1f p2)
| while_true(c: Cond)(b: Program): SS (Program.whilee c b) (Program.seq b (Program.whilee c b))
| while_false(c: Cond)(b: Program): SS (Program.whilee c b) Program.skip

-- true if state1 program1 can be transformed to state2 program2
def aSSOS(state1: State)(program1: Program)
         (state2: State)(program2: Program): Prop :=
         (∀sFin:State, BSOS state1 program1 sFin ↔ BSOS state2 program2 sFin) ∧
         (SS program1 program2)

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
  apply SS.assign

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
  apply SS.seq

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
  apply SS.seqSkip

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
  apply SS.if_true

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
  apply SS.if_false

def final(_: State)(program: Program): Prop := program = Program.skip

def blocked(state: State)(program: Program): Prop :=
  ¬(∃s2:State, ∃p2:Program, aSSOS state program s2 p2)

lemma blockerFinal(st: State)(prog: Program):
  (final st prog) ↔ (blocked st prog) := by
  rw [final, blocked]
  revert st
  induction prog with
  | skip =>
    intro st1
    simp
    intro st2
    intro prog
    rw [aSSOS]
    have neq:¬(SS Program.skip prog) := by
      by_contra h
      cases h
    aesop
  | assign name expr =>
    intro st
    simp
    exists replS st name (evalE expr st)
    exists Program.skip
    apply aSSOS_assign
  | seq p1 p2 ih1 ih2 =>
    sorry
  | iff =>
    sorry
  | whilee =>
    sorry
