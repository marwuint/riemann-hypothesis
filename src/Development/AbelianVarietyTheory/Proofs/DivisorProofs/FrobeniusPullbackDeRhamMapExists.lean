import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.LinFrob

open GlobalTheory.Twist GlobalTheory.ConjSeq

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (c : primDR A) :
    (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (frobDR p R hR A c) =
      frobDR p R' hR' A' ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull _ _ k (fun r ↦ ?_) (GlobalTheory.VB.frob_naturality p _ φ _) c).symm
  rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]

theorem frobDR_smul (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A : Over (Sp R)} [GrpObj A] (r : R) (c : primDR A) :
    frobDR p R hR A (r • c) = r ^ p • frobDR p R hR A c := by
  rw [LinearMap.map_smulₛₗ, frobR_apply]

end GlobalTheory.LinFrob
