import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalVolumePositivity

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.LocalBesselAndTopKernel Formalism.QuantumDeterminants NumberField IsDedekindDomain ValuativeRel
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem Dstar_pos (D : D7) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem section_exists : ∀ (k r : ℕ) (L : LocBessel k r), 1 ≤ k → ∃ μsec, IsSection k r L.z L.z' μsec
  | 0, _, _, h => absurd h (by norm_num)
  | _ + 1, _, L, _ => Formalism.MainNotions.S.Inh.big_cell_section_of_local_bessel L

theorem ptEntry_col {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ j, j < (bs.map Prod.snd).sum → ∃ i, i < (bs.map Prod.snd).sum ∧ ∃ t : K, t ≠ 0 ∧
      ∀ j', ptEntry bs i j' = if j' = j then t else 0
  | [], _, j, hj => absurd hj (by simp)
  | (t, s) :: rest, h, j, hj => by
    simp only [List.map_cons, List.sum_cons] at hj ⊢
    by_cases hjs : j < s
    · refine ⟨s - 1 - j, by omega, t, (h (t, s) (by simp)).1, fun j' => ?_⟩
      simp only [ptEntry]
      by_cases hj' : j' = j
      · subst hj'
        rw [if_pos ⟨by omega, hjs⟩, if_pos (by omega), if_pos rfl]
      · rw [if_neg hj']
        by_cases h2 : j' < s
        · rw [if_pos ⟨by omega, h2⟩, if_neg (by omega)]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => by omega)]
    · obtain ⟨i0, hi0, t0, ht0, h0⟩ := ptEntry_col rest (fun b hb => h b (by simp [hb])) (j - s) (by omega)
      refine ⟨i0 + s, by omega, t0, ht0, fun j' => ?_⟩
      simp only [ptEntry]
      rw [if_neg (fun hh => by omega)]
      by_cases h2 : s ≤ j'
      · rw [if_pos ⟨by omega, h2⟩, Nat.add_sub_cancel, h0]
        by_cases hj' : j' = j
        · rw [if_pos (by omega), if_pos hj']
        · rw [if_neg (by omega), if_neg hj']
      · rw [if_neg (fun hh => h2 hh.2), if_neg (by omega)]

theorem ptMat_det_ne {K : Type} [Field K] {n : ℕ} (p : Point K n) : (ptMat p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  funext j
  obtain ⟨i, hi, t, ht, hcol⟩ := ptEntry_col p.1 p.2.1 j.val (by rw [p.2.2]; exact j.2)
  have h1 := congrFun h0 ⟨i, by rw [← p.2.2]; exact hi⟩
  simp only [Matrix.mulVec, dotProduct, ptMat, hcol, Pi.zero_apply] at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg (fun hh => hb (Fin.ext hh)), zero_mul])
    (fun hh => absurd (Finset.mem_univ j) hh), if_pos rfl] at h1
  exact (mul_eq_zero.1 h1).resolve_left ht

theorem Dmin_top_ne (w : Point D.host.E (D.R.rS + 1)) : LocalSplitGroups.Dmin w (D.R.rS + 1) ≠ 0 := by
  unfold LocalSplitGroups.Dmin
  rw [dif_pos le_rfl]
  have : (ptMat w).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))) = ptMat w := by
    ext a b; rfl
  rw [this]
  exact ptMat_det_ne w

end Formalism.MainNotions.BridgeLemma

end
