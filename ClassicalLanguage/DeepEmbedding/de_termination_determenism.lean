import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.de_basic
import ClassicalLanguage.DeepEmbedding.de_BSOS
import ClassicalLanguage.DeepEmbedding.de_unlooping

theorem determenistic(prog: Program):
  ∀sStart sFin1 sFin2:State, (noLoop prog) → (BSOS sStart prog sFin1) → (BSOS sStart prog sFin2) → (sFin1 = sFin2) := by
  induction prog with
  | skip =>
    intro sStart
    intro sFin1
    intro sFin2
    intro
    intro h1
    intro h2
    cases h1
    cases h2
    simp
  | assign name expr =>
    intro sStart
    intro sFin1
    intro sFin2
    intro
    intro h1
    intro h2
    cases h1
    cases h2
    simp
  | seq p1 p2 determen1 determen2 =>
    intro sStart
    intro sFinVariant1
    intro sFinVariant2

    intro nlp
    have nlp1 : noLoop p1 := by
      apply And.left
      apply nlp
    have nlp2 : noLoop p2 := by
      apply And.right
      apply nlp
    clear nlp

    intro h1
    cases h1
    case seq sIntermed1 tr1_1 tr1_2 =>
    intro h2
    cases h2
    case seq sIntermed2 tr2_1 tr2_2 =>
    have intereq: sIntermed1 = sIntermed2 := by
      apply determen1 sStart
      apply nlp1
      apply tr1_1
      apply tr2_1
    clear determen1
    clear tr1_1
    clear tr2_1
    apply determen2 sIntermed1
    apply nlp2
    apply tr1_2
    rw [intereq]
    apply tr2_2
  | iff cond pt pf detpt detpf =>
    intro sStart
    intro sFinV1
    intro sFinV2

    intro nlp
    have nlpt : noLoop pt := by
      apply And.left
      apply nlp
    have nlpf : noLoop pf := by
      apply And.right
      apply nlp
    clear nlp

    intro h1
    intro h2
    cases h1
    case if_true condVal1 tr1t =>
      cases h2
      case if_true condVal2 tr2t =>
        clear condVal2
        apply detpt sStart
        apply nlpt
        apply tr1t
        apply tr2t
      case if_false condVal2 tr2f =>
        clear tr1t tr2f detpt detpf
        apply False.elim
        contradiction
    case if_false condVal1 tr1f =>
      cases h2
      case if_true condVal2 tr2t =>
        clear detpt detpf
        apply False.elim
        contradiction
      case if_false condVal2 tr2f =>
        apply detpf sStart
        apply nlpf
        apply tr1f
        apply tr2f
  | whilee c body ih =>
    simp [noLoop]

theorem terminates(prog: Program):
  ∀sStart, (noLoop prog) → (∃sFin: State, BSOS sStart prog sFin) := by
  induction prog with
  | skip =>
    intro sStart
    intro nlp
    exists sStart
    apply BSOS.skip
  | assign name expr =>
    intro sStart
    intro nlp
    clear nlp
    exists (replS sStart name (evalE expr sStart))
    apply BSOS.assign
  | seq p1 p2 ih1 ih2 =>
    intro sStart

    intro nlp
    have nlp1 : noLoop p1 := by
      apply And.left
      apply nlp
    have nlp2 : noLoop p2 := by
      apply And.right
      apply nlp
    clear nlp

    have termp1: ∃ sFin, BSOS sStart p1 sFin := by
      apply ih1
      apply nlp1
    clear ih1
    clear nlp1
    let ⟨sInter, exsInter⟩ := termp1
    clear termp1

    have termp2: ∃ sFin, BSOS sInter p2 sFin := by
      apply ih2
      apply nlp2
    clear ih2
    clear nlp2
    let ⟨sFinal, exsFinal⟩ := termp2
    clear termp2

    exists sFinal
    apply BSOS.seq p1 p2 sStart sInter sFinal
    apply exsInter
    apply exsFinal
  | iff cond pt pf termpt termpf =>
    intro sStart

    intro nlp
    have nlpt : noLoop pt := by
      apply And.left
      apply nlp
    have nlpf : noLoop pf := by
      apply And.right
      apply nlp
    clear nlp

    have lemt: ∃ sFint, BSOS sStart pt sFint := by
      apply termpt
      apply nlpt
    clear termpt
    clear nlpt
    let ⟨sFint, exsFint⟩ := lemt
    clear lemt

    have lemf: ∃ sFinf, BSOS sStart pf sFinf := by
      apply termpf
      apply nlpf
    clear termpf
    clear nlpf
    let ⟨sFinf, exsFinf⟩ := lemf
    clear lemf

    cases condVal: (evalC cond sStart)
    case true =>
      exists sFint
      apply BSOS.if_true
      apply condVal
      apply exsFint
    case false =>
      exists sFinf
      apply BSOS.if_false
      simp
      apply condVal
      apply exsFinf

  | whilee c body ih =>
    simp [noLoop]
