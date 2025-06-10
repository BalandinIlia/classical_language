import ClassicalLanguage.ShallowEmbedding.Expression
import ClassicalLanguage.ShallowEmbedding.Condition

namespace SE

-- This type represents all syntactically correct programs
inductive Program
| skip: Program
| assign: String → Expr → Program
| seq: Program → Program → Program
| iff: Cond → Program → Program → Program
| whilee: Cond → Program → Program
