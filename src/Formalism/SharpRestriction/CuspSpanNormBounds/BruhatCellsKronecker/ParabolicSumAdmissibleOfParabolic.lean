import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.S.UnitaryVolumeMass MeasureTheory Formalism.QuantumDeterminants
open scoped ENNReal InnerProductSpace

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsNormSq_eq_sum (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

def hsVec (A : Wq →L[ℂ] Wp) : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))

theorem hsVec_norm_sq (A : Wq →L[ℂ] Wp) : ‖hsVec A‖ ^ 2 = hsNormSq A := by
  rw [hsNormSq_eq_sum, PiLp.norm_sq_eq_of_L2]
  rfl

theorem hsNormSq_real_smul (c : ℝ) (A : Wq →L[ℂ] Wp) : hsNormSq (((c : ℝ) : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [_root_.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end HS

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

theorem jhUnit_le {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (νR : Measure (Mt D.R.k D.R.rS))
    (γ : MatKR D.R.k D.R.rS) (wt B : ℝ) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (wt * hsNormSq (A.J νR γ)) ≤ ENNReal.ofReal B * MMv D w w' A μsec) :
    wt * hsNormSq (jhUnit D w w' A μsec νR γ) ≤ B := by
  unfold jhUnit
  rw [hsNormSq_real_smul]
  by_cases hM : (MMv D w w' A μsec).toReal = 0
  · rw [hM, Real.zero_rpow (by norm_num)]
    simpa using hB
  · have hpos : 0 < (MMv D w w' A μsec).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
    have htop : MMv D w w' A μsec ≠ ⊤ := fun e => hM (by rw [e]; rfl)
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hB] at h
    have h2 : wt * hsNormSq (A.J νR γ) ≤ B * (MMv D w w' A μsec).toReal :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hpos.le)).1 h
    have h3 : ((MMv D w w' A μsec).toReal ^ (-(1 / 2 : ℝ))) ^ 2 = ((MMv D w w' A μsec).toReal)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
      norm_num
    rw [h3]
    calc wt * (((MMv D w w' A μsec).toReal)⁻¹ * hsNormSq (A.J νR γ))
        = (wt * hsNormSq (A.J νR γ)) * ((MMv D w w' A μsec).toReal)⁻¹ := by ring
      _ ≤ (B * (MMv D w w' A μsec).toReal) * ((MMv D w w' A μsec).toReal)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hpos.le)
      _ = B := by field_simp

end Rec

end Formalism.MainNotions.BridgeLemma

end
