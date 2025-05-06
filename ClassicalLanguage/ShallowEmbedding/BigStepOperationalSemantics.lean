import ClassicalLanguage.State.State
import ClassicalLanguage.ShallowEmbedding.Expression
import ClassicalLanguage.ShallowEmbedding.Condition
import ClassicalLanguage.ShallowEmbedding.Program

-- BSOS is an abbreviation: Big Step Operational Semantics
-- BSOS s1 p s2 means that execution of program p in state s1 can result in state s2.
-- However, in our case (determenistic language) it means that it results in s2.
inductive BSOS: State → Program → State → Prop
| skip(s:State):
      BSOS s Program.skip s
| assign(name: String)(expr: Expr)(s:State):
      BSOS s (Program.assign name expr) (replS s name (evalE expr s))
-- seq stays for "sequence"
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
