import Mathlib.Data.Int.Basic
import Aesop
import ClassicalLanguage.State.State
import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition
import ClassicalLanguage.DeepEmbedding.Program

open DE

-- SSOS means "small step operational semantics"
inductive SSOS: State → Program → State → Program → Prop
| skip         (s: State):
      SSOS s Program.skip s Program.skip
| assign       (s: State)(name: String)(expr: Expr):
      SSOS s (Program.assign name expr) (replS s name (evalE expr s)) Program.skip
| seq_skip     (s: State)(p: Program):
      SSOS s (Program.seq Program.skip p) s p
| seq          (s1 s2: State)(p1s p1f p2: Program):
      SSOS s1 p1s s2 p1f →
      SSOS s1 (Program.seq p1s p2) s2 (Program.seq p1f p2)
| if_true      (s: State)(cond: Cond)(pt pf: Program):
        evalC cond s →
        SSOS s (Program.iff cond pt pf) s pt
| if_false     (s: State)(cond: Cond)(pt pf: Program):
        ¬(evalC cond s) →
        SSOS s (Program.iff cond pt pf) s pf
| while_true   (s: State)(cond: Cond)(body: Program):
        evalC cond s →
        SSOS s (Program.whilee cond body) s (Program.seq body (Program.whilee cond body))
| while_false  (s: State)(cond: Cond)(body: Program):
        ¬(evalC cond s) →
        SSOS s (Program.whilee cond body) s Program.skip

-- this is configuration of a system with two concurrently executing programs
structure Conf where
s: State
p1: Program
p2: Program

inductive TransS: Conf → Conf → Prop
| left(s1 s2: State)(p1s p1f p2: Program):
    SSOS s1 p1s s2 p1f → TransS (Conf.mk s1 p1s p2) (Conf.mk s2 p1f p2)
| right(s1 s2:State)(p1 p2s p2f: Program):
    SSOS s1 p2s s2 p2f → TransS (Conf.mk s1 p1 p2s) (Conf.mk s2 p1 p2f)

inductive TransClos: Conf → Conf → Prop
| oneStep(c1 c2: Conf):
      TransS c1 c2 → TransClos c1 c2
| sevStep(c1 cInter c2: Conf):
      TransClos c1 cInter →
      TransClos cInter c2 →
      TransClos c1 c2

-- Proposition that given configuration may execute in given state
def results(init: Conf)(s: State):Prop := TransClos init (Conf.mk s Program.skip Program.skip)

def stateAB: ℤ → ℤ → State
| a, b => (fun s:String => if(s="a") then a else if (s="b") then b else 0)

def p1:Program := Program.assign "a" (Expr.num 1)

def p2:Program := (Program.iff
                             (Cond.less (Expr.var "a") (Expr.num 1))
                             (Program.assign "b" (Expr.num 1))
                             (Program.assign "b" (Expr.num 2))
                  )

def exampl:Conf := Conf.mk (stateAB 0 0) p1 p2

theorem th1: results exampl (stateAB 1 1) := by
      let conf1:Conf := exampl
      let conf2:Conf := Conf.mk (stateAB 0 0) p1 (Program.assign "b" (Expr.num 1))
      let conf3:Conf := Conf.mk (stateAB 1 0) Program.skip (Program.assign "b" (Expr.num 1))
      let conf4:Conf := Conf.mk (stateAB 1 1) Program.skip Program.skip

      rw [results]
      have eq1: exampl = conf1 := by
            aesop
      have eq2: Conf.mk (stateAB 1 1) Program.skip Program.skip = conf4 := by
            aesop
      rw [eq1, eq2]
      clear eq1 eq2

      apply TransClos.sevStep conf1 conf3 conf4
      apply TransClos.sevStep conf1 conf2 conf3

      apply TransClos.oneStep
      apply TransS.right
      apply SSOS.if_true
      simp [evalC, evalE, stateAB]

      apply TransClos.oneStep
      apply TransS.left
      rw [p1]
      have repl1: stateAB 1 0 = replS (stateAB 0 0) "a" 1 := by
            simp [replS, stateAB]
      rw [repl1]
      clear repl1
      apply SSOS.assign

      apply TransClos.oneStep
      apply TransS.right
      have repl2: stateAB 1 1 = replS (stateAB 1 0) "b" 1 := by
            clear conf1 conf2 conf3 conf4
            simp [replS, stateAB]
            funext s
            cases eq: s=="a"
            case true =>
                  simp at eq
                  simp [eq]
            case false =>
                  simp at eq
                  simp [eq]
      rw [repl2]
      clear repl2
      apply SSOS.assign

theorem th2: results exampl (stateAB 1 2) := by
      let conf1:Conf := exampl
      let conf2:Conf := Conf.mk (stateAB 1 0) Program.skip p2
      let conf3:Conf := Conf.mk (stateAB 1 0) Program.skip (Program.assign "b" (Expr.num 2))
      let conf4:Conf := Conf.mk (stateAB 1 2) Program.skip Program.skip

      rw [results]
      have eq1: exampl = conf1 := by
            aesop
      have eq2: Conf.mk (stateAB 1 2) Program.skip Program.skip = conf4 := by
            aesop
      rw [eq1, eq2]
      clear eq1 eq2

      apply TransClos.sevStep conf1 conf3 conf4
      apply TransClos.sevStep conf1 conf2 conf3

      apply TransClos.oneStep
      apply TransS.left
      rw [p1]
      have repl1: stateAB 1 0 = replS (stateAB 0 0) "a" 1 := by
            simp [replS, stateAB]
      rw [repl1]
      clear repl1
      apply SSOS.assign

      apply TransClos.oneStep
      apply TransS.right
      rw [p2]
      apply SSOS.if_false
      simp [evalC, evalE, stateAB]

      apply TransClos.oneStep
      apply TransS.right
      have repl2: stateAB 1 2 = replS (stateAB 1 0) "b" 2 := by
            simp [replS, stateAB]
            clear conf1 conf2 conf3 conf4
            funext s
            cases eq1:s=="a"
            case true =>
                  simp [] at eq1
                  simp [eq1]
            case false =>
                  simp [] at eq1
                  simp [eq1]
      rw [repl2]
      clear repl2
      apply SSOS.assign
