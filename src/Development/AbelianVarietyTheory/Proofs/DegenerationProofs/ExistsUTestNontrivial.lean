import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegenerateTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

open IsLocalRing in

theorem exists_padic_embedding (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (h : Finite (ResidueField V)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : FractionRing V →+* PadicAlgCl p),
      ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  obtain ⟨p, _, K₀, e, e₀, -, he⟩ := completeDVR_eq_integralClosure_padicInt.1 V (FractionRing V) h
  refine ⟨p, inferInstance, (algebraMap K₀ (PadicAlgCl p)).comp e.toRingHom, fun x => ?_⟩
  refine (mem_integralClosure_padicInt_iff K₀ (e x)).symm.trans ⟨fun hx => ⟨e₀.symm ⟨e x, hx⟩, ?_⟩, ?_⟩
  · apply e.injective
    rw [he, e₀.apply_symm_apply]
  · rintro ⟨v, rfl⟩
    rw [he]
    exact (e₀ v).2

end GlobalTheory.DegenerateTest

end
