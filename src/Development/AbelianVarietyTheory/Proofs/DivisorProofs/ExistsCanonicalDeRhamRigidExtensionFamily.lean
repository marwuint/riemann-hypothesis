import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtension
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DeRhamExt

def canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : primDR A →ₗ[R] G.RigExt :=
  Classical.choose (_root_.GlobalTheory.PtExt.exists_canMap R A p G t hA)

theorem isCan_iff_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A)
    (x : G.RigExt) : IsCan t c x ↔ canMap p hA t c = x :=
  Classical.choose_spec (_root_.GlobalTheory.PtExt.exists_canMap R A p G t hA) c x

theorem isCan_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A) :
    IsCan t c (canMap p hA t c) :=
  (isCan_iff_canMap p hA t c _).2 rfl

theorem canMap_bijective (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] {R : Type}
    [CommRing R] (hR : IsNilpotent (p : R)) {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : Function.Bijective (canMap p hA t) := by
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham hP p R hR A hA G t
  exact _root_.GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham hP p R hR A g hA hg G t _ (isCan_canMap p hA t)

def canFamily (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] :
    GlobalTheory.Published.DeRhamVectorExtension.Family p :=
  fun _ _ hR _ _ hA _ t => LinearEquiv.ofBijective (canMap p hA t) (canMap_bijective hP p hR hA t)

theorem exists_canonical_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime],
    ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧
      ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
        (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A),
        IsCan t c (e hR hA t c) := by
  intro hP p _
  refine ⟨canFamily hP p, ?_, ?_, ?_, ?_⟩
  · intro R R' _ _ hR hR' A _ A' _ hA hA' G G' t t' σ φ m c
    exact ((isCan_iff_canMap p hA' t' _ _).1
      (_root_.GlobalTheory.PtExtNat.isCan_pull p R R' A A' G G' t t' σ φ m c _ (isCan_canMap p hA t c)))
  · intro R _ hR A _ hA G t
    obtain ⟨N, hN⟩ := hR
    exact GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms p R N hN A hA G t (canMap p hA t)
      (canMap_bijective hP p ⟨N, hN⟩ hA t).2 (isCan_canMap p hA t)
  · intro R _ hR A _ hA G t h v
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham hP p R hR A hA G t
    exact _root_.GlobalTheory.PtExt.isLieImage_iff_lieCorr hP p R hR A g hA hg G t (canFamily hP p hR hA t)
      (isCan_canMap p hA t) h v
  · intro R _ hR A _ hA G t c
    exact isCan_canMap p hA t c

end GlobalTheory.DeRhamExt
