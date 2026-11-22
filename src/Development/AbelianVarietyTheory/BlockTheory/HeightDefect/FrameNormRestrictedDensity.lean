import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Core D}

abbrev GenericFrames (T : Core D) (j : ℕ) : Type :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))

def ConstBound (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) (C A P : ℝ) (n : ℕ) (wL : WeightFamilies.Wt D j) : Prop :=
  WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size ≤ P * n * wL.size

end GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity
