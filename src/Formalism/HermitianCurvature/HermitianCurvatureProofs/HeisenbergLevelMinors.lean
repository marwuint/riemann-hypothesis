import Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfJqSmoothOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma norm_le_gN (M : Mat k r) : ‖M‖ ≤ gN M := by
  have hg : gN M = Real.sqrt (∑ i, ∑ j, Complex.normSq (M i j)) := rfl
  rw [hg, Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  have h2 : ‖M i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (M i j) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = |‖M i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ _ := Real.abs_le_sqrt h2

lemma gN_unit {X : Mat k r} (hX : ∀ i j, ‖X i j‖ ≤ 1) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have hg : gN X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := rfl
  have h1 : ∀ i j, Complex.normSq (X i j) ≤ 1 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hX i j, norm_nonneg (X i j)]
  have hs : (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc (∑ i, ∑ j, Complex.normSq (X i j))
        ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hg]
  calc Real.sqrt _ ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_mul_self (Nat.cast_nonneg _)

lemma gN_conjT (M : Mat k r) : gN Mᴴ = gN M := by
  show Real.sqrt _ = Real.sqrt _
  congr 1
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

private lemma gN_mul_le_hermitian_curvature (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  have hA : gN A = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := rfl
  have hB : gN B = Real.sqrt (∑ i, ∑ j, Complex.normSq (B i j)) := rfl
  have hAB : gN (A * B) = Real.sqrt (∑ i, ∑ j, Complex.normSq ((A * B) i j)) := rfl
  have hSA : 0 ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have entry : ∀ i j, Complex.normSq (∑ l, A i l * B l j) ≤
      (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l‖ * ‖B l j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖A i l‖) (fun l => ‖B l j‖)
    have h3 : ∀ l, Complex.normSq (A i l) = ‖A i l‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    have h4 : ∀ l, Complex.normSq (B l j) = ‖B l j‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    simp only [h3, h4]
    have h5 : ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
      have := norm_nonneg (∑ l, A i l * B l j)
      nlinarith
    exact h5.trans h2
  have hS : (∑ i, ∑ j, Complex.normSq ((A * B) i j)) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
   calc (∑ i, ∑ j, Complex.normSq ((A * B) i j))
      = ∑ i, ∑ j, Complex.normSq (∑ l, A i l * B l j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          congrArg Complex.normSq Matrix.mul_apply
    _ ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
    _ = (∑ i, ∑ l, Complex.normSq (A i l)) * (∑ j, ∑ l, Complex.normSq (B l j)) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (B l j))]
  rw [hA, hB, hAB]
  exact (Real.sqrt_le_sqrt hS).trans (le_of_eq (Real.sqrt_mul hSA _))

lemma gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le_hermitian_curvature _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
