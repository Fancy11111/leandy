import Leandy.Generalities.Order
import Leandy.Core.Trace.Types

/-- Defines the notation for corruption -/
class Corrupt (α₀ α η:Type) [eqα: DecidableEq α] [eqβ: DecidableEq η] [instP: Parameter α] where
  corrupt: α₀ → 𝑇 α η → Prop
  monotone (x:α₀) : Monotone (corrupt x)

/-- since it's corrupted IT'S RADIOACTIVE !!!! -/
infix:50 " ☢ " => Corrupt.corrupt
