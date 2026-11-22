import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PrCloudAddPrNode
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.LowVec

variable {k r : ℕ}

abbrev flagSpan (k r : ℕ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1))

theorem mem_flagSpan {a : Fin (r + 1)} {y : Fin (2 * r + k + 1) → ℂ} :
    y ∈ flagSpan k r a ↔ ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
  constructor
  · intro hy i hi
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have := b.2
      exact Pi.single_eq_of_ne (fun e => by rw [e] at hi; simp only [eI] at hi; omega) _
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : a.val ≤ i.val
    · rw [hy i hi, Pi.single_zero]; exact Submodule.zero_mem _
    · have ha := a.isLt
      have : (Pi.single i (y i) : Fin (2 * r + k + 1) → ℂ) = y i • bvec (eI k r ⟨i.val, by omega⟩) := by
        rw [bvec, ← Pi.single_smul, smul_eq_mul, mul_one]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, by simpa using hi⟩, rfl⟩)

theorem mulVec_sub {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z)
    (a : Fin (r + 1)) {y : Fin (2 * r + k + 1) → ℂ} (hy : y ∈ flagSpan k r a) :
    ∃ y' ∈ flagSpan k r a, s *ᵥ (fvec k r z a - y) = fvec k r z a - y' := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hc := ((WeylGroupFacts.nset_iff m).1 hm).2
  have ha := a.isLt
  have h1 : fvec k r z a - m *ᵥ (fvec k r z a - y) ∈ flagSpan k r a := by
    refine mem_flagSpan.2 fun i hi => ?_
    have : (m *ᵥ (fvec k r z a - y)) i = ((1 : Mat k r) *ᵥ (fvec k r z a - y)) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val ≤ r + k ∧ (j.val ≤ i.val ∨ r ≤ i.val)
      · rw [hc i j hj.1 hj.2, Matrix.one_apply]
      · have e1 : y j = 0 := mem_flagSpan.1 hy j (by omega)
        have e2 : fvec k r z a j = 0 := by
          unfold fvec
          split_ifs with h'
          · exact Pi.single_eq_of_ne (fun e => by rw [e] at hj; simp only [eI] at hj; omega) _
          · exact hz j (by omega)
        simp [e1, e2]
    rw [Pi.sub_apply, this, Matrix.one_mulVec, Pi.sub_apply, mem_flagSpan.1 hy i hi]; ring
  have h2 : ∀ x ∈ flagSpan k r a, h *ᵥ x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact (hh.2.1 b.1).1
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  have h3 : h *ᵥ fvec k r z a = fvec k r z a := by
    unfold fvec
    split_ifs with h'
    · exact (hh.2.1 _).1
    · exact hh.2.2
  refine ⟨_, h1, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have := h2 _ h1
  rw [Matrix.mulVec_sub, h3] at this
  rw [sub_sub_cancel]
  exact sub_right_injective this

theorem lA_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z) (g : Mat k r)
    (a : Fin (r + 1)) : lA k r z (s * g) a = lA k r z g a := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hu : IsUnit s.det := by
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    rw [Matrix.det_mul]
    exact ((uHGroup _ _ hH).2.2 h hh.1).1.mul ((uHGroup _ _ hH).2.2 m hm.1).1
  unfold lA
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz ((sGroup k r z hz).2.2 s hs) a hy
    exact ⟨y', hy', by rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, e]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz hs a hy
    refine ⟨y', hy', ?_⟩
    rw [← e, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem eucl_unitary {N : ℕ} {t : Matrix (Fin N) (Fin N) ℂ} (ht : t ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (v : Fin N → ℂ) : eucl (t *ᵥ v) = eucl v := by
  have e : ∀ v : Fin N → ℂ, ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := fun v => by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  have h1 : tᴴ * t = 1 := Matrix.mem_unitaryGroup_iff'.1 ht
  unfold eucl
  congr 1
  apply Complex.ofReal_injective
  rw [e, e, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]

theorem lA_right (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) {t : Mat k r}
    (ht : t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lA k r z (g * t) a = lA k r z g a := by
  have h1 : t⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ht)]
    exact Unitary.star_mem ht
  unfold lA
  simp only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, eucl_unitary h1]

end GlobalTheory.Mom.LowVec
