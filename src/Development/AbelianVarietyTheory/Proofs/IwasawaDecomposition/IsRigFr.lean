import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayHoriz

section Jet

variable {S : Type} [CommRing S] {ρ : Type}

def jetW {K : Type} [Fintype K] (w : K → ρ → S) (m : ℕ) : Jet S ρ m →ₐ[S] Jet S (K × ρ) m :=
  jetMap (fun r => ∑ i, MvPolynomial.C (w i r) * MvPolynomial.X (i, r)) fun r =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (X_mem_orig (i, r))

end Jet

end GlobalTheory.RayHoriz
