import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosets
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.GoodOut

open GlobalTheory.Points

theorem exists_hom_ker {R : Type} [CommRing R] (z : PrimeSpectrum R) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (f : R →+* K), ∀ t, f t = 0 ↔ t ∈ z.asIdeal :=
  ⟨AlgebraicClosure z.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap z.asIdeal.ResidueField _).comp (algebraMap R z.asIdeal.ResidueField), fun _ =>
    (map_eq_zero_iff (algebraMap z.asIdeal.ResidueField _) (RingHom.injective _)).trans
      Ideal.algebraMap_residueField_eq_zero⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem exists_th_notMem (hL : Laws) (hL₂ : Laws2) (ρ : S.Real) (z : PrimeSpectrum S.R) (a : S.Gam) :
    ∃ c : S.Gam, ρ.n • c = 0 ∧ (⟨S.th (a + c), S.th_mem _⟩ : S.R) ∉ z.asIdeal := by
  obtain ⟨K, _, _, f, hf⟩ := exists_hom_ker z
  let x : Sp K ⟶ Sp S.R := spMap f
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n * ρ.n ^ (j - 1 + ρ.k * 2) := by
    rw [hr, ρ.N_eq, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hn : (ρ.n : K) ≠ 0 := by
    have h := (S.unit.map (f.comp (algebraMap o S.R))).ne_zero
    rw [map_natCast, hM, Nat.cast_mul] at h
    exact left_ne_zero_of_mul h
  obtain ⟨θ, hθ, hv⟩ := UnitTheta.exists_sec_of_baseOver S.R ρ.P ρ.th₁
  obtain ⟨y₀, hy₀, e₀⟩ := ThetaFibre.exists_mem_nonzeroLocus_fibre hL₂.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
    (x (IsLocalRing.closedPoint K))
  let u : Over.mk x ⟶ baseOver (Sp S.R) := Over.homMk x (by simp)
  obtain ⟨y, hy, H⟩ := UnitTheta.exists_good_point_of_sec hL.polBaseChange hL.goodPt _ ρ.P θ K x ρ.n
    ρ.n_prime.two_le hn ⟨_, hθ y₀ hy₀, _, e₀.symm⟩ (u ≫ ρ.pt a)
  have := ρ.P.isAb.comm
  obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul ρ.pt ρ.pt_add
  obtain ⟨c, hc, -⟩ := ρ.pt_bij K x y (by rw [hM, pow_mul, hy, one_pow])
  obtain ⟨a₀, -, uniq⟩ := ρ.pt_bij K x 1 (one_pow _)
  refine ⟨c, (uniq _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
    (uniq _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun h => ?_⟩
  have e : (u ≫ ρ.pt a * y).left = spMap f ≫ (ρ.pt (a + c)).left := by
    rw [← hc, ρ.pt_add]
    exact congrArg CommaMorphism.left (MonObj.comp_mul u _ _).symm
  rw [e] at H
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (H (x := IsLocalRing.closedPoint K) trivial)
  have hk' := (le_preimage_iff _ _).2 hk
  have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hk'
  refine ((le_preimage_basicOpen_iff _ hU _).1 hk').ne_zero ?_
  rw [hv _ _ _ (ρ.th_val (a + c)) K f k hU, (hf _).2 h, zero_mul]

section Transfer

variable {Z : Scheme.{0}} (P : PolAV Z)

def sect : P.A.left ⟶ (baseOver Z ⊗ P.A).left := (lift (toUnit P.A) (𝟙 P.A) : P.A ⟶ baseOver Z ⊗ P.A).left

theorem sect_snd : sect P ≫ (snd (baseOver Z) P.A).left = 𝟙 _ := by
  rw [sect, ← Over.comp_left, lift_snd, Over.id_left]

instance isIso_snd : IsIso (snd (baseOver Z) P.A).left := inferInstanceAs (IsIso (pullback.snd (𝟙 Z) P.A.hom))

instance isIso_sect : IsIso (sect P) := IsIso.of_isIso_fac_right (sect_snd P)

end Transfer

variable (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩)

end GlobalTheory.ZH.GoodOut

end
