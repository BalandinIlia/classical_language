import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.de_basic
import ClassicalLanguage.DeepEmbedding.de_BSOS

def noLoop: Program → Prop
| Program.skip          =>   true
| Program.assign _ _    =>   true
| Program.seq p1 p2     =>   (noLoop p1) ∧ (noLoop p2)
| Program.iff _ p1 p2   =>   (noLoop p1) ∧ (noLoop p2)
| Program.whilee _ _    =>   false

def seqq: Program → ℕ → Program
| _, 0 => Program.skip
| p, (Nat.succ n) => Program.seq (seqq p n) p

def unlooped: Program → Program → Prop
| (Program.whilee _ body), unl =>
    ∃bodyUnl: Program, ∃n:ℕ,
      (unlooped body bodyUnl) ∧ (unl = seqq bodyUnl n)
| (Program.iff cond bt bf), (Program.iff condu btu bfu) =>
    cond = condu ∧ (unlooped bt btu) ∧ (unlooped bf bfu)
| (Program.seq b1 b2), (Program.seq b1u b2u) =>
    (unlooped b1 b1u) ∧ (unlooped b2 b2u)
| (Program.assign n e), (Program.assign nu eu) => (n=nu)∧(e=eu)
| Program.skip, Program.skip => true
| _, _ => false

theorem unloop(prog: Program):
  ∀ sStart sFin: State, (BSOS sStart prog sFin) →
                        (∃ progNLP: Program, BSOS sStart progNLP sFin ∧ noLoop progNLP) := by
  intro sStart sFin
  intro BSOS1
  induction BSOS1 with
  | while_true cond prog1 s1 s2 s3 condVal tr1 tr2Raw ih1 ih2 =>

    let prog2:Program := (Program.whilee cond prog1)
    have tr2 : BSOS s2 prog2 s3 := by
      simp [prog2]
      apply tr2Raw
    clear tr2Raw

    let ⟨progNLP1, propProgNLP1⟩ := ih1
    let ⟨progNLP2, propProgNLP2⟩ := ih2
    clear ih1 ih2

    exists (Program.seq progNLP1 progNLP2)

    apply And.intro
    {
      apply BSOS.seq progNLP1 progNLP2 s1 s2 s3
      apply And.left
      apply propProgNLP1
      apply And.left
      apply propProgNLP2
    }
    {
      rw [noLoop]
      apply And.intro
      apply And.right
      apply propProgNLP1
      apply And.right
      apply propProgNLP2
    }
  | while_false =>
    exists Program.skip
    apply And.intro
    apply BSOS.skip
    simp [noLoop]
  | skip =>
    exists Program.skip
    apply And.intro
    apply BSOS.skip
    simp [noLoop]
  | assign name expr =>
    exists (Program.assign name expr)
    apply And.intro
    apply BSOS.assign
    simp [noLoop]
  | seq p1 p2 s1 s2 s3 tr1 tr2 ih1 ih2 =>

    let ⟨progNLP1, propProgNLP1⟩ := ih1
    let ⟨progNLP2, propProgNLP2⟩ := ih2
    clear ih1 ih2

    exists (Program.seq progNLP1 progNLP2)

    apply And.intro
    {
      apply BSOS.seq progNLP1 progNLP2 s1 s2 s3
      apply And.left
      apply propProgNLP1
      apply And.left
      apply propProgNLP2
    }
    {
      simp [noLoop]
      apply And.intro
      apply And.right
      apply propProgNLP1
      apply And.right
      apply propProgNLP2
    }
  | if_true cond progt progf s1 s2 condVal trt ih =>
    let ⟨progNLPt, propProgNLPt⟩ := ih
    clear ih
    exists progNLPt
  | if_false cond progt progf s1 s2 condVal trt ih =>
    let ⟨progNLPf, propProgNLPf⟩ := ih
    clear ih
    exists progNLPf
