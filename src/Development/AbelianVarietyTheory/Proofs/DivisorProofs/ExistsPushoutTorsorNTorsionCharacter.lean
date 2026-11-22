import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocOfIsSecDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAddOfIsSecDiffIsSecAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), (n : R) = 0 → HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (_root_.GlobalTheory.PtExt.PushSec.exists_isSec R A n hR b hb D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (_root_.GlobalTheory.PtExt.PushSec.exists_isSec R A n hR b hb D x)
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.PtExt.exists_isSecDiff R A n hR b hb S hS
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.PtExt.exists_isSecAdd R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
