import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.SphPar

theorem dualLab_splitLab_getD (n k : ℕ) (i : ℕ) :
    (dualLab (splitLab n k)).getD i 0 = if i < k then 1 else 0 := by
  have h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0 := by
    simp [dualLab, splitLab]
  rw [h]
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem diagonal_dualLab_splitLab {L : Type} [Field L] (n k : ℕ) (ϖ : L) :
    Matrix.diagonal (fun i : Fin n => ϖ ^ (dualLab (splitLab n k)).getD i 0) = diagJ n ϖ k := by
  unfold diagJ
  congr 1
  funext i
  rw [dualLab_splitLab_getD]
  split_ifs <;> simp

theorem Tj_eq_of_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ ϖ' : P.adicCompletion E} (h : IsUnifV E P ϖ) (h' : IsUnifV E P ϖ') :
    Tj ℂ n (Ov E P) ϖ' k = Tj ℂ n (Ov E P) ϖ k := by
  unfold IsUnifV at h h'
  have hv0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hv0' : Valued.v ϖ' ≠ 0 := by rw [h']; exact WithZero.coe_ne_zero
  have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have h0' : ϖ' ≠ 0 := fun e => hv0' (by rw [e, map_zero])
  have hu : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, h', ← h, div_self hv0]
  have e : ϖ' = ϖ' / ϖ * ϖ := (div_mul_cancel₀ _ h0).symm
  rw [e]
  refine Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])

theorem divInd_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ : P.adicCompletion E} (h : IsUnifV E P ϖ) :
    divInd (n := n) (Ov E P) (dualLab (splitLab n k)) = Tj ℂ n (Ov E P) ϖ k := by
  funext g
  by_cases hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g
  · obtain ⟨ϖ', h', hab⟩ := id hg
    rw [diagonal_dualLab_splitLab] at hab
    rw [← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg),
      Set.indicator_of_mem (by exact hab)]
  · rw [divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]
    intro hab
    refine hg ⟨ϖ, h, ?_⟩
    rw [diagonal_dualLab_splitLab]
    exact hab

end GlobalTheory.SphPar
