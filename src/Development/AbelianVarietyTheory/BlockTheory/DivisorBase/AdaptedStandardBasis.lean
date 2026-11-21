import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

def polyNorm {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : ℝ :=
  Real.sqrt (∑ s : c.F →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)

variable {Xo c} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end Family

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData
