import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def sabMapCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t' : SAB H S'}
    {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' := h ▸ m

theorem sabMapCast_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : (sabMapCast m h).φ = m.φ := by
  subst h
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
