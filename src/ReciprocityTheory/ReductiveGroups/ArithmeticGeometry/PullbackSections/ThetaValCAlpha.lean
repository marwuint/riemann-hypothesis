import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def vspActL {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) :
    ReciprocityTheory.ChartRestriction.G.I2.Vsp dim →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp dim where
  toFun := ReciprocityTheory.ChartRestriction.G.I2.act α
  map_add' v w := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act, mul_add]
  map_smul' c v := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act]
    ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections
