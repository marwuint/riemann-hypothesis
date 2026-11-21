import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReFrameIffReframeIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReframeCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.PjFree (FrBaseChg ReFrame XoNumPt TanLin SClause IntRebase)

export GlobalTheory.ReframeClauses (isTanAt_of_isCombAt isEigAt_of_isCombAt)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

end GlobalTheory.ReframeCompare
