import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLineLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem mem_frameStab_of_parFlag {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {L : Matrix (Fin s) (Fin n) E} (hL : L * C = 1)
    {d : Fin s → ℕ} {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) : g ∈ frameStab σ J C ⊤ := by
  obtain ⟨⟨B, -, e⟩, B', -, e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  exact ⟨⟨B, B', hBB, mul_eq_one_comm.1 hBB⟩, Subgroup.mem_top _, e⟩

omit [NumberField E] in

theorem unipRad_fix {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h, Units.val_one, Matrix.mul_one]⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [e, Subgroup.mem_bot.1 hB, Units.val_one, Matrix.mul_one]

end GlobalTheory.ResLineLevi
