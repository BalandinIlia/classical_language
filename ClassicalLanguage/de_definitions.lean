import Mathlib.Data.Nat.Basic
import Aesop

def State := String → ℤ

def replS: State → String → ℤ → State
| st, name, val => (fun s:String => if(s==name) then val else st s)

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
| eq: Expr → Expr → Cond
| not: Cond → Cond
| and: Cond → Cond → Cond
| or: Cond → Cond → Cond

def evalC: Cond → State → Bool
| Cond.truee, _          =>   true
| Cond.falsee, _         =>   false
| (Cond.eq e1 e2), st    =>   (evalE e1 st) == (evalE e2 st)
| (Cond.not c), st       =>   not (evalC c st)
| (Cond.and c1 c2), st   =>   and (evalC c1 st) (evalC c2 st)
| (Cond.or c1 c2), st    =>   or (evalC c1 st) (evalC c2 st)

def replC: Cond → String → Expr → Cond
| Cond.truee, _, _               =>   Cond.truee
| Cond.falsee, _, _              =>   Cond.falsee
| (Cond.eq e1 e2), name, eSub    =>   Cond.eq (replE e1 name eSub) (replE e2 name eSub)
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
  | eq e1 e2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement]
  | not c ih =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih]
  | and c1 c2 ih1 ih2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
    simp [evalC, replC, replE, evalE, replS, exprReplacement, ih1, ih2]

inductive Program
| skip: Program
| assign: String → Expr → Program
| seq: Program → Program → Program
| iff: Cond → Program → Program → Program
| whilee: Cond → Program → Program

def noLoop: Program → Prop
| Program.skip          =>   true
| Program.assign _ _    =>   true
| Program.seq p1 p2     =>   (noLoop p1) ∧ (noLoop p2)
| Program.iff _ p1 p2   =>   (noLoop p1) ∧ (noLoop p2)
| Program.whilee _ _    =>   false

inductive BSOS: State → Program → State → Prop
| skip(s:State):
      BSOS s Program.skip s
| assign(name: String)(expr: Expr)(s:State):
      BSOS s (Program.assign name expr) (replS s name (evalE expr s))
| seq(p1 p2: Program)(s1 s2 s3: State):
      BSOS s1 p1 s2 →
      BSOS s2 p2 s3 →
      BSOS s1 (Program.seq p1 p2) s3
| if_true(c: Cond)(pt pf: Program)(s1 s2: State):
      evalC c s1 →
      BSOS s1 pt s2 →
      BSOS s1 (Program.iff c pt pf) s2
| if_false(c: Cond)(pt pf: Program)(s1 s2: State):
      ¬(evalC c s1) →
      BSOS s1 pf s2 →
      BSOS s1 (Program.iff c pt pf) s2
| while_true(c: Cond)(body: Program)(s1 s2 s3: State):
      evalC c s1 →
      BSOS s1 body s2 →
      BSOS s2 (Program.whilee c body) s3 →
      BSOS s1 (Program.whilee c body) s3
| while_false(c: Cond)(body: Program)(s: State):
      ¬(evalC c s) →
      BSOS s (Program.whilee c body) s

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

-- HOARE LOGIC

def hoare(P: Cond)(prog: Program)(Q: Cond): Prop := 
    ∀sStart sFin: State, evalC P sStart → BSOS sStart prog sFin → evalC Q sFin

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
