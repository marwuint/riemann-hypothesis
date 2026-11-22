import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.FormalDegreeBessel.StatementBF
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DecreasingNodeGaps

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient

open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

variable {k r : ℕ}

def IsClosedMatGroup (U : Set (Mat k r)) : Prop :=
  IsClosed U ∧ (1 : Mat k r) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
    ∀ a ∈ U, IsUnit a.det ∧ a⁻¹ ∈ U

def IsHaarOn (U : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop :=
  μ {x | Matrix.of x ∉ U} = 0 ∧ (∀ a ∈ U, μ.map (lmulM a) = μ) ∧
    (∀ C : Set (Mt k r), IsCompact C → (∀ x ∈ C, Matrix.of x ∈ U) → μ C < ⊤) ∧ μ ≠ 0

def leviW (k r : ℕ) (s : Mat k r) : Mat k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j
  else if i = j then 1 else 0

section Twist

variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def IsEquivariant (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (φ : Mat k r → Wp) : Prop :=
  ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ g ∈ UH (Hpk k r),
    φ (h * n * g) = psiGen k r z c n • π h (φ g)

def sectionL2NormSq (ν : Measure (Mt k r)) (φ : Mat k r → Wp) : ℝ≥0∞ :=
  ∫⁻ g, ‖φ (Matrix.of g)‖ₑ ^ 2 ∂ν

end Twist

theorem col_of_fix {h : Mat k r} {j : Fin (2 * r + k + 1)}
    (hj : h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have := congrFun hj i
  simpa [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, Pi.single_apply] using this

theorem col_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  apply col_of_fix
  by_cases h1 : j.val < r
  · have := (hh.2.1 ⟨j.val, h1⟩).1
    simpa [Formalism.QuantumDeterminants.eI] using this
  · have h2 : 2 * r + k - j.val < r := by omega
    have := (hh.2.1 ⟨_, h2⟩).2
    have e : Formalism.QuantumDeterminants.esI k r ⟨_, h2⟩ = j := by
      apply Fin.ext; simp only [Formalism.QuantumDeterminants.esI]; omega
    rwa [e] at this

theorem Hpk_row {i i' : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k))
    (e : i.val + i'.val = 2 * r + k) (l : Fin (2 * r + k + 1)) :
    Hpk k r i' l = if l = i then 1 else 0 := by
  unfold Hpk
  have := l.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem row_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have hlt := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have e : i.val + i'.val = 2 * r + k := by simp only [i']; omega
  have hi' : ¬ (r ≤ i'.val ∧ i'.val ≤ r + k) := by omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have h1 := congrFun (congrFun hU i') j
  have hrow : ∀ m, (hᴴ * Hpk k r) i' m = Hpk k r i' m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, col_out hh hi']
    rw [Finset.sum_eq_single i'] <;> simp +contextual
  rw [Matrix.mul_apply] at h1
  simp only [hrow, Hpk_row hi e] at h1
  simpa [eq_comm] using h1

theorem leviW_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : leviW k r (h * n) = h := by
  funext i j
  unfold leviW
  split_ifs with h1 h2
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hn.2.2 j j h1.2.1 h1.2.2 h1.2.1]; simp
    · intro l _ hl
      by_cases hr : r ≤ l.val
      · rw [hn.2.2 l j h1.2.1 h1.2.2 hr]; simp [hl]
      · rw [col_out hh (j := l) (by omega) i, if_neg, zero_mul]
        rintro rfl
        omega
    · simp
  · subst h2
    rw [col_out hh (j := i) (by tauto) i]; simp
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [row_out hh (i := i) (by tauto) j, if_neg h2]
    · rw [col_out hh hj i, if_neg h2]

end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient

end
