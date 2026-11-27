import Theorems.FermatLittleTheorem.A
import Theorems.FermatLittleTheorem.B

namespace TuriMath.FermatLittleTheorem

/-- Statements A and B agree: unfold both and transport hypotheses/conclusions. -/
theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h p hp a
    exact h p hp a
  · intro h p hp a
    exact h p hp a

end TuriMath.FermatLittleTheorem
