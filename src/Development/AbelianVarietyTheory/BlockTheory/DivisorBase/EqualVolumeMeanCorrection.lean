import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.DegreeFormula.FlagDegFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Formalism.MainNotions.DIV.Align Filter Topology

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection

open Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr

section One
variable {D : D7} (Y : ShimX D.what₂.Tau)

def IsSlope (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (c : Y.Comp) (a : ℝ) : Prop :=
  (∀ᶠ s : ℚ in 𝓝[>] 0, 0 < Y.geoC (Y.Mbar B u s) c) ∧
    Tendsto (fun s : ℚ => Y.arSelfC (Y.Mbar B u s) c /
      (((dimY Y : ℝ) + 1) * Y.geoC (Y.Mbar B u s) c)) (𝓝[>] 0) (𝓝 a)

end One

end GlobalTheory.IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection

end
