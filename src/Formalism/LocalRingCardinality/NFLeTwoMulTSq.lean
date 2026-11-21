import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

namespace Formalism.BasicNotions

theorem ParamsT.nV_eq {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.R.nV = T.TO * T.nWn + (8 * D.R.f * D.R.r + 4) := by
  have h1 := T.split
  have h2 := T.nP_eq
  unfold Ranks.nV
  omega

theorem ParamsT.nV_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ D.R.nV := by
  rw [T.nV_eq]; exact Nat.le_add_left _ _

end Formalism.BasicNotions
