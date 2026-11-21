import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinatePolynomialBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem exists_log_lift {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (hz : ‖z‖ < 1 / 2) (h0 : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) :
    ∃ s ∈ logDom n a, logExp a s = z ∧ (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) ∧
      1 + ‖s‖ ≤ 5 * (1 + |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖|) := by
  classical
  set s : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k with hs
  have hzk : ∀ k, ‖z k‖ < 1 / 2 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz
  have hpos : ∀ k : Fin n, (k : ℕ) < a → 0 < ‖z k‖ := fun k hk => norm_pos_iff.mpr (h0 k hk)
  have hlogneg : ∀ k : Fin n, (k : ℕ) < a → Real.log ‖z k‖ < 0 := fun k hk =>
    Real.log_neg (hpos k hk) (by linarith [hzk k])
  set ℓ := |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖| with hℓ
  have hℓk : ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖z k‖ ≤ ℓ := by
    intro k hk
    rw [hℓ, norm_prod, Real.log_prod]
    · calc -Real.log ‖z k‖ ≤ ∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), -Real.log ‖z j‖ := by
            apply Finset.single_le_sum (f := fun j => -Real.log ‖z j‖)
            · intro j hj
              have := hlogneg j (Finset.mem_filter.mp hj).2
              linarith
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        _ = -∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), Real.log ‖z j‖ := by
            rw [Finset.sum_neg_distrib]
        _ ≤ _ := neg_le_abs _
    · intro j hj
      exact (hpos j (Finset.mem_filter.mp hj).2).ne'
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true, hs]
      rw [Complex.log_re]
      exact hlogneg k hk
    · simp only [hk, if_false, hs]
      linarith [hzk k]
  · funext k
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true, hs]
      exact Complex.exp_log (h0 k hk)
    · simp only [logExp, hk, if_false, hs]
  · intro j hj
    simp only [hj, if_true, hs]
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  · have hsk : ∀ k, ‖s k‖ ≤ ℓ + 4 := by
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [hk, if_true, hs]
        have h1 : ‖Complex.log (z k)‖ ≤ |(Complex.log (z k)).re| + |(Complex.log (z k)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h1
        have h2 : |Real.log ‖z k‖| = -Real.log ‖z k‖ := abs_of_neg (hlogneg k hk)
        have h3 := Complex.abs_arg_le_pi (z k)
        have h4 := hℓk k hk
        linarith [Real.pi_lt_four]
      · simp only [hk, if_false, hs]
        linarith [hzk k]
    have : ‖s‖ ≤ ℓ + 4 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr hsk
    linarith

theorem eventually_entries_le {V m n : Type} [TopologicalSpace V] [Fintype m] [Fintype n] {W : V → Matrix m n ℂ} {b₀ : V}
    (h : ContinuousAt W b₀) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ ≤ M := by
  classical
  have hij : ∀ i j, ∀ᶠ b in 𝓝 b₀, ‖W b i j‖ < ‖W b₀ i j‖ + 1 := by
    intro i j
    have hc : ContinuousAt (fun b => ‖W b i j‖) b₀ :=
      continuous_norm.continuousAt.comp ((continuous_id.matrix_elem i j).continuousAt.comp h)
    exact hc.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨∑ i, ∑ j, (‖W b₀ i j‖ + 1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have hall : ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ < ‖W b₀ i j‖ + 1 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hij i j
    filter_upwards [hall] with b hb i j
    calc ‖W b i j‖ ≤ ‖W b₀ i j‖ + 1 := (hb i j).le
      _ ≤ ∑ j', (‖W b₀ i j'‖ + 1) :=
          Finset.single_le_sum (f := fun j' => ‖W b₀ i j'‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖W b₀ i' j'‖ + 1) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖W b₀ i' j'‖ + 1))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem differentiableOn_finset_prod {V J : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {u : Finset J} {f : J → V → ℂ}
    {B : Set V} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) B) : DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) B := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert i u hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i u)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.ShFam.Hor
