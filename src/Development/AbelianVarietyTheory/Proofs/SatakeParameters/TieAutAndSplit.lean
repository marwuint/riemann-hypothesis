import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvalues
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AutomorphismSplitting

theorem isCSD_inv' {R : Ranks} {H : Host R} {χ : HChar H.E} (h : IsCSD H χ) : IsCSD H χ⁻¹ :=
  ⟨fun w w' hw k => congrArg (·⁻¹) (h.1 w w' hw k), fun k => congrArg (·⁻¹) (h.2 k)⟩

theorem hasInf_inv {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L}
    (h : χ.HasInf φ (fun _ => 1)) : (χ⁻¹).HasInf φ (fun _ => -1) := by
  intro k
  have hk := h k
  show (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val, hk, ← Finset.prod_inv_distrib]
  simp

end GlobalTheory.AutomorphismSplitting
