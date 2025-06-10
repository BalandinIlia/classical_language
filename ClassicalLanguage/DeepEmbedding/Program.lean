import ClassicalLanguage.DeepEmbedding.Expression
import ClassicalLanguage.DeepEmbedding.Condition

namespace DE

-- This type represents all syntactically correct programs
inductive Program
| skip: Program
| assign: String → Expr → Program
| seq: Program → Program → Program
| iff: Cond → Program → Program → Program
| whilee: Cond → Program → Program
