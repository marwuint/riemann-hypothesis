import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ChowHt GlobalTheory.ProjSpace

namespace projTuple

instance isIso_bcFst : IsIso ((projSys ℚ 1).bcFst ℚ) := by
  have : IsIso (spMap (algebraMap ℚ ℚ)) := by
    rw [show spMap (algebraMap ℚ ℚ) = 𝟙 _ from Spec.map_id _]
    infer_instance
  exact inferInstanceAs (IsIso (pullback.fst _ _))

end projTuple

end GlobalTheory.Adelic
