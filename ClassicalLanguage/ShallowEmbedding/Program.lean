import ClassicalLanguage.ShallowEmbedding.Expression
import ClassicalLanguage.ShallowEmbedding.Condition

namespace SE

inductive Program
| skip: Program
| assign: String → Expr → Program
| seq: Program → Program → Program
| iff: Cond → Program → Program → Program
| whilee: Cond → Program → Program
