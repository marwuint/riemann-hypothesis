import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.Push

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
variable {ι : Type} [Fintype ι] {X : ι → Type} {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)] in
private theorem lmarginal_prod_eq_prod_lintegral_mul_prod [DecidableEq ι] (f : (i : ι) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (s : Finset ι) (x : (i : ι) → X i) :
    (∫⋯∫⁻_s, (fun z => ∏ i, f i (z i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ y, f i y ∂(μ i)) * ∏ i ∈ sᶜ, f i (x i) := by
  have hF : Measurable fun z : (i : ι) → X i => ∏ i, f i (z i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert i s hi ih =>
    rw [lmarginal_insert _ hF hi]
    simp_rw [ih]
    have h : ∀ y, ∏ j ∈ sᶜ, f j (Function.update x i y j) =
        f i y * ∏ j ∈ (insert i s)ᶜ, f j (x j) := by
      intro y
      rw [Finset.compl_insert, ← Finset.mul_prod_erase _ _ (Finset.mem_compl.2 hi),
        Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp_rw [h]
    rw [Finset.prod_insert hi, lintegral_const_mul _ ((hf i).mul_const _),
      lintegral_mul_const _ (hf i)]
    ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
theorem _root_.GlobalTheory.SnMass.Push.lintegral_fintype_prod {ι : Type} [Fintype ι] {X : ι → Type}
    {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  by_cases hne : ∀ i, Nonempty (X i)
  · rw [lintegral_eq_lmarginal_univ (fun i => (hne i).some), lmarginal_prod_eq_prod_lintegral_mul_prod f hf]
    simp
  · push_neg at hne
    obtain ⟨i, hi⟩ := hne
    haveI : IsEmpty ((i : ι) → X i) := ⟨fun x => hi.elim (x i)⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.eq_zero_of_isEmpty (μ i)])]
    simp [Measure.eq_zero_of_isEmpty (Measure.pi μ)]

end GlobalTheory.SnMass.Push
