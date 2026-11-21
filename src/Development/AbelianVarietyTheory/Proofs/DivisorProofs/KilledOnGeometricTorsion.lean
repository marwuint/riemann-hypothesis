import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceOfIsConnected

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionRigid

variable {S : Scheme.{0}}

instance mono_ι (G : Over S) [GrpObj G] (N : ℕ) : Mono (torsion.ι G N) := by
  have : Mono η[G] := ⟨fun _ _ _ => toUnit_unique _ _⟩
  exact inferInstanceAs (Mono (pullback.fst _ _))

end GlobalTheory.TorsionRigid

namespace GlobalTheory.TorsionRigid

end GlobalTheory.TorsionRigid
