import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem compact_to_unitary_hermitian (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P)
    (hg : g ∈ Formalism.REAL.Kset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∩
      (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have a1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have a2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have iP : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv a1
  have gJ : g.conjTranspose * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (Formalism.REAL.maximal_compact_facts _ ε).1 g hg
  rw [iP]
  constructor
  · show (P.conjTranspose * g * P).conjTranspose * Formalism.QuantumDeterminants.Hpk k r * (P.conjTranspose * g * P) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP.1.2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P.conjTranspose * (g.conjTranspose * P) * (P.conjTranspose * Formalism.REAL.Jm ε * P) * (P.conjTranspose * g * P)
        = P.conjTranspose * (g.conjTranspose * ((P * P.conjTranspose) * Formalism.REAL.Jm ε * (P * P.conjTranspose)) * g) * P := by
          simp only [Matrix.mul_assoc]
      _ = P.conjTranspose * Formalism.REAL.Jm ε * P := by
          rw [a2, Matrix.one_mul, Matrix.mul_one, gJ, Matrix.mul_assoc]
  · have hs : P.conjTranspose ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hP.2
    exact mul_mem (mul_mem hs hg.1) hP.2

end Formalism.MainNotions.BridgeLemma

end
