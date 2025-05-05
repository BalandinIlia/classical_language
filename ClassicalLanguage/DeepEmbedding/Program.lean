import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition

inductive Program
| skip: Program
| assign: String → Expr → Program
| seq: Program → Program → Program
| iff: Cond → Program → Program → Program
| whilee: Cond → Program → Program
