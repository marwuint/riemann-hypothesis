import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymmPoincare

universe u

section Swap

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A B : Over S} [GrpObj A] [GrpObj B]

theorem isCorrForm_swap {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) : IsCorrForm κ t B A (swap P) (-φ.flip) := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  have m : IsMor κ ((A ⊗ B).hom ≫ t) κ ((B ⊗ A).hom ≫ t) (RingHom.id R) (lift (snd B A) (fst B A)).left :=
    (homMor κ t (lift (snd B A) (fst B A))).isMor
  have k := isChern_pull m hc
  rw [crystallinePull2_sum_cup] at k
  refine ⟨n, fun i ↦ -b i, a, ?_, fun x y ↦ ?_⟩
  · convert k using 2 with i
    rw [pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, Submodule.coe_neg, map_neg, map_neg,
      LinearMap.neg_apply, neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφ, map_neg, ← Finset.sum_neg_distrib, neg_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem isCorrForm_of_iso {P Q : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : IsCorrForm κ t A B Q φ := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  exact ⟨n, a, b, (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ hP hQ e _ hc, hφ⟩

theorem skew_of_symm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P)
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x :=
  LinearMap.congr_fun₂ (H.unique C hP (isCorrForm_of_iso (isCorrForm_swap H) (pull_isLB hP _) hP hs)) x y

end Swap

end GlobalTheory.SymmPoincare
