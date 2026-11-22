import Mathlib
import Formalism.SharpRestriction.Divisibility.FlipOneTwo
import Formalism.DegreeFormula.PointDegree.FlagDeg
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

structure JetSit (D : D7) (P : ModuliIntegralCharts.Prov D) (l q DF : ℕ) where
  w : P.Dat
  y : (P.loc w l).Pt (P.loc w l).Xm
  nW : ℕ
  hq : ModuliIntegralCharts.NHyp D l q
  hDF : 3 * DF + 2 ≤ q
  sg : (P.loc w l).At y ((P.loc w l).latStd nW) q → (P.loc w l).Th y ((P.loc w l).latStd nW) q
  hsg : (P.loc w l).SymLift y ((P.loc w l).latStd nW) q sg
  ev : (P.loc w l).Jet y ((P.loc w l).latStd nW) q DF →ₗ[((P.loc w l).fld y).C] ((P.loc w l).fld y).C

section SizesF

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end SizesF

end Formalism.MainNotions.DIV

end

namespace Formalism.MainNotions.DIV

end Formalism.MainNotions.DIV
