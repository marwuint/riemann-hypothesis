import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CcARatioZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Weighted
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import Formalism.PeriodIntegrals.ZuckTensor

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem cns_data {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)),
      StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
      (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, h1, h2, h3, h4, -, h6, h7, h8⟩ := S7.psiAll ε lam h T hlam hh hq
  have hmax := hth
  unfold thrStar at hmax
  rw [max_lt_iff] at hmax
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ (n : ℝ) * S7.q0 ε := by positivity
  have hL2 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith [hmax.2]
  have hw2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith [hmax.2]
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hmax.1⟩
  have hP : IsPsiFor ε lam T Ψ := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 hL2⟩
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have := T.w_norm
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨m, hm⟩ := S7.exists_mu hlam
  refine ⟨T, Ψ, hgap, hP, hv₀, psi_exp_isPositive T Ψ m hm (h8 m hm), ?_, hasGelfandChar_sigLam hgap hP hv₀ h7⟩
  exact weighted_datum hgap hP hv₀ (fun μ hμ => (h6 μ hμ).2.2 2 (by norm_num) hw2)

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

end ReciprocityTheory.ChartRestriction.DS

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem cns_single_bd (s x : Fin n) : 0 ≤ (Pi.single s (1 : ℝ) : Fin n → ℝ) x ∧
    (Pi.single s (1 : ℝ) : Fin n → ℝ) x ≤ 1 := by
  by_cases h : x = s
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem cns_single_01 (s x : Fin n) : (Pi.single s (1 : ℝ) : Fin n → ℝ) x = 0 ∨
    (Pi.single s (1 : ℝ) : Fin n → ℝ) x = 1 := by
  by_cases h : x = s
  · right; subst h; simp
  · left; simp [Pi.single_eq_of_ne h]

theorem cns_shift_gap (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hh : GapAtLeast ε μ h)
    (s : Fin n) : GapAtLeast ε (shiftF dual μ s) (h - 1) := by
  intro a b hab
  have h0 := hh a b hab
  obtain ⟨a0, a1⟩ := cns_single_bd s a
  obtain ⟨b0, b1⟩ := cns_single_bd s b
  cases dual
  · simp only [shiftF, cond_false, Pi.add_apply]
    have e : μ a + (Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ b + (Pi.single s (1 : ℝ) : Fin n → ℝ) b) =
        (μ a - μ b) - -((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) := by ring
    rw [e]
    have := abs_sub_abs_le_abs_sub (μ a - μ b)
      (-((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b))
    have hd : |-((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b)| ≤ 1 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  · simp only [shiftF, cond_true, Pi.sub_apply]
    have e : μ a - (Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ b - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) =
        (μ a - μ b) - ((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) := by ring
    rw [e]
    have := abs_sub_abs_le_abs_sub (μ a - μ b)
      ((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b)
    have hd : |(Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b| ≤ 1 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith

theorem cns_sing (dual : Bool) {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) {s : Fin n}
    (hns : ¬ S7.IsHCParam (shiftF dual μ s)) : ¬ Function.Injective (shiftF dual μ s) := by
  intro hinj
  apply hns
  constructor
  · intro a b hab
    obtain ⟨ma, hma⟩ := hμ.2 a
    obtain ⟨mb, hmb⟩ := hμ.2 b
    have hlt := hμ.1 hab
    have h1 : μ b + 1 ≤ μ a := by
      have hz : mb < ma := by
        have : (mb : ℝ) < ma := by linarith
        exact_mod_cast this
      have hz' : mb + 1 ≤ ma := Int.add_one_le_iff.mpr hz
      have : ((mb + 1 : ℤ) : ℝ) ≤ (ma : ℝ) := by exact_mod_cast hz'
      push_cast at this
      linarith
    obtain ⟨a0, a1⟩ := cns_single_bd s a
    obtain ⟨b0, b1⟩ := cns_single_bd s b
    have hle : shiftF dual μ s b ≤ shiftF dual μ s a := by
      cases dual
      · simp only [shiftF, cond_false, Pi.add_apply]; linarith
      · simp only [shiftF, cond_true, Pi.sub_apply]; linarith
    exact lt_of_le_of_ne hle (fun e => hab.ne' (hinj e))
  · intro a
    obtain ⟨ma, hma⟩ := hμ.2 a
    rcases cns_single_01 s a with h0 | h0
    · refine ⟨ma, ?_⟩
      cases dual
      · simp only [shiftF, cond_false, Pi.add_apply, h0]; linarith
      · simp only [shiftF, cond_true, Pi.sub_apply, h0]; linarith
    · cases dual
      · refine ⟨ma + 1, ?_⟩
        simp only [shiftF, cond_false, Pi.add_apply, h0]; push_cast; linarith
      · refine ⟨ma - 1, ?_⟩
        simp only [shiftF, cond_true, Pi.sub_apply, h0]; push_cast; linarith

end ReciprocityTheory.ChartRestriction.DS
