import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.Model

open NumberField IsDedekindDomain Module Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Steps

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem hasPts (h : Laws U x) (Z : Comp Xo c) : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z

end Steps

end GlobalTheory.FlatCore.Model

end
