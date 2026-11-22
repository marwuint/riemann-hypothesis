import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Formalism.PeriodIntegrals.QuotInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.GramExp

def GDef {N a : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (X : Fin N → Fin a → ℂ) : Prop :=
  ((Matrix.of X)ᴴ * H * Matrix.of X).det ≠ 0 ∧ PosOnPerp H (Matrix.of X)

def GGram {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (a : ℕ) : Set (HCo a) :=
  {t | ∃ X : Fin N → Fin a → ℂ, (Matrix.of X)ᴴ * H * Matrix.of X = hOf t ∧ GDef H X}

def Sgn {a : ℕ} (d : Fin a → ℂ) : Prop := ∀ i, d i = 1 ∨ d i = -1

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.diag_sq {a : ℕ} {d : Fin a → ℂ}
    (hd : _root_.GlobalTheory.GramExp.Sgn d) : Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.GramExp.isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H * H = 1) : _root_.PI.IsMatGroup (_root_.Formalism.QuantumDeterminants.UH H) := by
  unfold _root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH
  have hdetH : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hH
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det := by
    intro a ha
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have h1 : aᴴ.det * a.det = 1 := by
      have : (aᴴ.det * a.det) * H.det = 1 * H.det := by linear_combination this
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hu := hunit a ha
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    have hc : (a⁻¹)ᴴ * aᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = ((a⁻¹)ᴴ * aᴴ) * H * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hc, hr, Matrix.one_mul, Matrix.mul_one]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.exp_cont {n : ℕ} :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.GramExp.measurableSet_image_ball {X Y : Type} [PseudoMetricSpace X] [ProperSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y}
    (hf : Continuous f) (x : X) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1)) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hb, Set.image_iUnion]
  exact MeasurableSet.iUnion fun k =>
    ((isCompact_closedBall x _).image hf).isClosed.measurableSet

end GlobalTheory.GramExp
