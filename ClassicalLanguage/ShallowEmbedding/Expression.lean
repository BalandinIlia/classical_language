import Mathlib.Data.Int.Basic
import ClassicalLanguage.State.State

-- SE means "shallow embedding"
namespace SE

-- arithmetic expression
def Expr := State → Int
