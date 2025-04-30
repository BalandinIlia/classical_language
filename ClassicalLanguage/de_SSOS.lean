import Mathlib.Data.Nat.Basic
import Aesop
import ClassicalLanguage.de_basic

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
