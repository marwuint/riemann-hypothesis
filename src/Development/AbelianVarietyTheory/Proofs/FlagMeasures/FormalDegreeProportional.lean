import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem map_phi_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P Q : MatKR k r} (hP : IsCayley k r ε P)
    (hQ : IsCayley k r ε Q) : (Formalism.REAL.muG ε).map (phi ε P) = (Formalism.REAL.muG ε).map (phi ε Q) := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hQu, hQJ⟩ := hQ

  set Pu := hPu.unit with hPu_def
  set Qu := hQu.unit with hQu_def
  have hQQ : Q * Q⁻¹ = 1 := by
    rw [← hQu.unit_spec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmJ : (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = Formalism.REAL.Jm ε := by
    have h1 : (Q⁻¹)ᴴ * Qᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
    calc (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = (Q⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * Q⁻¹) := by
          rw [hPJ, ← hQJ]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h1, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hmem : Pu * Qu⁻¹ ∈ Formalism.REAL.UJ ε := by
    have hv : ((Pu * Qu⁻¹ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = P * Q⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv, hPu_def, hQu_def, hPu.unit_spec, hQu.unit_spec]
    show Formalism.REAL.inUJ ε _
    rw [hv]
    exact hmJ
  set m : Formalism.REAL.UJ ε := ⟨Pu * Qu⁻¹, hmem⟩ with hm_def
  have hval : ∀ (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hA : IsUnit A)
      (u : Formalism.REAL.UJ ε), phi ε A u = ((hA.unit⁻¹ * (u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) * hA.unit :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
    intro A hA u
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hA.unit_spec]
    rfl
  have hconj : phi ε Q = phi ε P ∘ (fun u => m * u * m⁻¹) := by
    funext u
    rw [Function.comp_apply, hval Q hQu, hval P hPu]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm_def]
    rw [hPu_def, hQu_def]
    group <;> rfl
  have hcont : ∀ A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Continuous (phi ε A) := by
    intro A
    have : Continuous (fun u : Formalism.REAL.UJ ε =>
        ((u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  have hinv : (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹) = Formalism.REAL.muG ε := by
    have hL : Measurable (fun u : Formalism.REAL.UJ ε => m * u) := measurable_const_mul m
    have hR : Measurable (fun u : Formalism.REAL.UJ ε => u * m⁻¹) := measurable_mul_const m⁻¹
    calc (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹)
        = ((Formalism.REAL.muG ε).map (fun u => m * u)).map (fun u => u * m⁻¹) := by
          rw [Measure.map_map hR hL]; rfl
      _ = (Formalism.REAL.muG ε).map (fun u => u * m⁻¹) := by
          rw [MeasureTheory.map_mul_left_eq_self (Formalism.REAL.muG ε) m]
      _ = Formalism.REAL.muG ε := Formalism.REAL.indefinite_unitary_unimodular _ ε m⁻¹
  rw [hconj, ← Measure.map_map (hcont P).measurable (by
    exact (measurable_const_mul m).mul_const m⁻¹), hinv]

end GlobalTheory.DegreeTie

end
