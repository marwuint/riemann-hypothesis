import Mathlib
import GroundTheory.AutomorphicForms.HaarSK
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectHaar

open MeasureTheory Measure Topology Set Function TopologicalSpace GroundTheory.Automorphic.HaarSK
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.NAK

theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) :
    μ.map (· * k) = μ := by
  obtain ⟨A, hA, hA1⟩ := exists_compact_mem_nhds (1 : G)
  set B : Set G := A * (K : Set G) with hB
  have hBc : IsCompact B := hA.mul hK
  have hAB : A ⊆ B := fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩
  have hpos : μ B ≠ 0 := (measure_pos_of_mem_nhds μ (Filter.mem_of_superset hA1 hAB)).ne'
  have hfin : μ B ≠ ∞ := hBc.measure_lt_top.ne
  have hpre : (fun x => x * k) ⁻¹' B = B := by
    ext x
    simp only [Set.mem_preimage, hB, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), by rw [← mul_assoc, he, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k, K.mul_mem hk' hk, by rw [← mul_assoc, he]⟩
  have h := map_right_mul_eq_modularCharacterFun_smul μ k
  have h2 := congrArg (fun m : Measure G => m B) h
  simp only [coe_nnreal_smul_apply] at h2
  rw [map_apply (measurable_mul_const k) hBc.measurableSet, hpre] at h2
  have h3 : modularCharacterFun k = 1 := by
    have : (modularCharacterFun k : ℝ≥0∞) * μ B = 1 * μ B := by rw [one_mul]; exact h2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 this
  rw [h, h3, one_smul]

end GlobalTheory.NAK
