import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isStandardSmooth_mvPolynomial (R σ : Type) [CommRing R] [Finite σ] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card σ) R (MvPolynomial σ R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial σ R) σ Empty :=
    { __ := Algebra.Generators.mvPolynomial R σ
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_pspace (R : Type) [CommRing R] (M : ℕ) :
    SmoothOfRelativeDimension M (PSpace.str R M) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} M)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension M))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} M) (chartCover R M)
    fun (i : Fin (M + 1)) => ?_
  change SmoothOfRelativeDimension M (chartι R M i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension M)).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := isStandardSmooth_mvPolynomial R {j : Fin (M + 1) // j ≠ i}
  rw [show Nat.card {j : Fin (M + 1) // j ≠ i} = M by simp] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap M).2 h

variable (k : Type) [Field k] (M : ℕ)

theorem geometricallyConnected_pspace : GeometricallyConnected (PSpace.str k M) :=
  ⟨geometrically_iff_of_commRing.2 fun K _ _ _ _ _ h =>
    have e := (isPullback_baseChange M (algebraMap k K)).isoIsPullback _ _ h
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous⟩

abbrev projSys : LinSys k where
  Y := PSpace k M
  str := PSpace.str k M
  D := M
  L := O1 k M
  isLB := O1_isLB k M
  N := M + 1
  b := coord k M

namespace projSys

abbrev gen : PSpace k M := AmpleModel.genericPt k M

theorem gen_mem (i : Fin (M + 1)) : gen k M ∈ chart k M i := fun h => X_ne_zero (R := k) i h

theorem valR_resPt {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U) (f : Γ(Y, U)) :
    valR (resPt y) U f = Y.evaluation U y hy f := by
  have ht : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := (le_preimage_iff (C := Y.presheaf.stalk y) _ U).2 (by
    rw [show Y.fromSpecStalk y (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y from
      Scheme.fromSpecStalk_closedPoint]; exact hy)
  have e : valMap (C := Y.presheaf.stalk y) (Y.fromSpecStalk y) U ht = Y.presheaf.germ U y hy := by
    change (Y.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact (valR_spMap_comp (Y.residue y).hom (Y.fromSpecStalk y) U ht f).trans (congrArg (Y.residue y).hom
    ((valR_eq (C := Y.presheaf.stalk y) _ _ ht f).trans (congrArg (fun q => q.hom f) e)))

end projSys
end GlobalTheory.Adelic
