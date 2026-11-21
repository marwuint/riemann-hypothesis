import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GlobalTheory.JSW

variable {n : ℕ}

def htGL (g : GL (Fin n) ℂ) : ℝ :=
  1 + ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ + ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖

def levSet (n r : ℕ) : Set (GL (Fin n) ℂ) :=
  {g | ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}

def rowCut (ρ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ := fun j => if j ≤ ρ then x ρ j else 0

def secMat (ρ j : Fin n) (v : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i l => if i = ρ then (if l ≤ ρ then v l else 0) else if l = Equiv.swap j ρ i then 1 else 0

open Classical in

def toGL (x : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n) ℂ := if h : IsUnit x then h.unit else 1

theorem val_toGL {x : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit x) : (toGL x : Matrix (Fin n) (Fin n) ℂ) = x := by
  simp [toGL, h]

theorem one_le_htGL (g : GL (Fin n) ℂ) : 1 ≤ htGL g := by
  unfold htGL
  have h1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  linarith

theorem htGL_pos (g : GL (Fin n) ℂ) : 0 < htGL g := lt_of_lt_of_le one_pos (one_le_htGL g)

theorem htGL_inv (g : GL (Fin n) ℂ) : htGL g⁻¹ = htGL g := by
  unfold htGL; rw [inv_inv]; ring

theorem sum_norm_mul_le (a b : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(a * b) i j‖ ≤ ∑ j, ∑ l, ‖a i l‖ * ‖b l j‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ = ∑ l, ‖a i l‖ * ∑ j, ‖b l j‖ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ l, ‖a i l‖ * ∑ l', ∑ j, ‖b l' j‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun l' => ∑ j, ‖b l' j‖) (fun _ _ => by positivity) (Finset.mem_univ l))
          (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem htGL_mul_le (g h : GL (Fin n) ℂ) : htGL (g * h) ≤ htGL g * htGL h := by
  unfold htGL
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have h1 := sum_norm_mul_le (g : Matrix (Fin n) (Fin n) ℂ) h
  have h2 := sum_norm_mul_le ((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (g⁻¹ : GL (Fin n) ℂ)
  have a1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a3 : 0 ≤ ∑ i, ∑ j, ‖(h : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a4 : 0 ≤ ∑ i, ∑ j, ‖((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  nlinarith [mul_nonneg a1 a4, mul_nonneg a2 a3]

theorem norm_entry_le_htGL (g : GL (Fin n) ℂ) (i j : Fin n) : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ htGL g := by
  unfold htGL
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h1 : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ i))
  linarith

theorem continuous_htGL : Continuous (htGL : GL (Fin n) ℂ → ℝ) := by
  have h1 : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) ℂ => ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    Units.continuous_coe_inv
  unfold htGL
  fun_prop

theorem isOpenEmbedding_valGL :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) ℂ => fun i j => (g : Matrix (Fin n) (Fin n) ℂ) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) ℂ)

theorem measurable_comp_GL {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) ℂ → β} (hF : Continuous F) {γ : X → GL (Fin n) ℂ}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGL.measurableEmbedding.measurable_comp_iff).1
    (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_dual {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {η : X → Z →L[ℝ] ℝ} (h : ∀ z, Measurable fun x => η x z) : Measurable η := by
  let b := Module.finBasis ℝ Z
  have : η = fun x => ∑ i, η x (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
    funext x
    ext z
    conv_lhs => rw [← b.sum_repr z, map_sum]
    simp only [map_smul]
    simp [mul_comm]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (h _).smul_const _

end GlobalTheory.JSW
