import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := IsAlgClosed.lift
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

end GlobalTheory.FieldSize
