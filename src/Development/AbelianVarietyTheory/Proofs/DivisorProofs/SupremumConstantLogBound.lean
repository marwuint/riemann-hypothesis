import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupConstSize

open NumberField MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.SupConstSize.finrank_eq_two_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ E = 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  have h := IsTotallyComplex.finrank E
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg
  omega

end GlobalTheory.SupConstSize

namespace GlobalTheory.SupConstSize
end GlobalTheory.SupConstSize

namespace GlobalTheory.SupConstSize
open Real

open NumberField MeasureTheory in
open scoped ENNReal in
open Real in

theorem _root_.GlobalTheory.SupConstSize.epsLev_bounds (E : Type) [Field E] [NumberField E] (d M : ℕ) (w : ℝ)
    (hf : 1 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ)) (hd : 1 ≤ d) (hM : 1 ≤ M) (hw : 1 ≤ w) :
    0 < _root_.GlobalTheory.LevGeo.epsLev E d M w ∧ _root_.GlobalTheory.LevGeo.epsLev E d M w ≤ 1 ∧
      1 / (3 * _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E * w * M * Real.sqrt d) ≤ _root_.GlobalTheory.LevGeo.epsLev E d M w := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hs : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd'
  have hA : 1 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w := one_le_mul_of_one_le_of_one_le hf hw
  have hB : 1 ≤ (M : ℝ) * Real.sqrt d := one_le_mul_of_one_le_of_one_le hM' hs
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpi := Real.pi_gt_three
  have hden : 0 < 2 * (M : ℝ) * Real.sqrt d * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w + 2) * 1 * Real.log 2 := by positivity
  have hpos : 0 < Real.pi / (2 * (M : ℝ) * Real.sqrt d * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w + 2) * 1 * Real.log 2) :=
    div_pos Real.pi_pos hden
  have e : 3 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w * M * Real.sqrt d = 3 * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w) * ((M : ℝ) * Real.sqrt d) := by
    ring
  unfold _root_.GlobalTheory.LevGeo.epsLev _root_.ReciprocityTheory.ChartRestriction.G.FD.epStar
  refine ⟨lt_min one_pos hpos, min_le_left _ _, le_min ?_ ?_⟩
  · rw [e, div_le_one (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 hB)]
  · rw [e, div_le_div_iff₀ (by positivity) hden]
    have hAB : 0 < (M : ℝ) * Real.sqrt d := by linarith
    have key : 2 * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w + 2) * Real.log 2 ≤ 3 * Real.pi * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w) := by
      nlinarith [mul_lt_mul_of_pos_left hl2 (by linarith : (0 : ℝ) < (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w),
        mul_lt_mul_of_pos_left hpi (by linarith : (0 : ℝ) < (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w)]
    have e1 : 1 * (2 * (M : ℝ) * Real.sqrt d * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w + 2) * 1 * Real.log 2) =
        ((M : ℝ) * Real.sqrt d) * (2 * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w + 2) * Real.log 2) := by ring
    have e2 : Real.pi * (3 * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w) * ((M : ℝ) * Real.sqrt d)) =
        ((M : ℝ) * Real.sqrt d) * (3 * Real.pi * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * w)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hAB.le

open NumberField MeasureTheory in
open scoped ENNReal in
open Real in

theorem _root_.GlobalTheory.SupConstSize.multBd_size (E : Type) [Field E] [NumberField E] (r : ℕ)
    (ε B : ℝ) (hf : 1 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ)) (hr : 1 ≤ (r : ℝ)) (hε : 0 < ε) (hB : 1 ≤ B) (hεB : 1 / B ≤ ε) :
    1 ≤ _root_.GlobalTheory.LevGeo.multBd E r ε ∧
      Real.log (_root_.GlobalTheory.LevGeo.multBd E r ε) ≤ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * (r : ℝ) ^ 2 *
        (Real.log 16 + 2 * (Real.log (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) + Real.log r) + Real.log (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) + Real.log B) := by
  refine ⟨_root_.GlobalTheory.LevGeo.one_le_multBd E r hε, ?_⟩
  have hdE : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dE
    have h : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast h
  have hB0 : 0 < B := by linarith
  have hinv : 1 / ε ≤ B := (one_div_le hε hB0).2 hεB
  have hX : 1 + 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E / ε ≤
      16 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * B := by
    have h1 : 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E / ε ≤
        8 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * B := by
      rw [div_eq_mul_one_div]
      calc 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * (1 / ε)
          ≤ 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * B :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 8 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * B := by ring
    have h2 : 1 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * B :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf) (one_le_pow₀ hr)) hdE) hB
    linarith
  have hpos : 0 < 1 + 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E / ε := by
    have : 0 ≤ 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E / ε := by
      have : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E := by linarith
      positivity
    linarith
  have hf0 : 0 < (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) := by linarith
  have hr0 : 0 < (r : ℝ) := by linarith
  have hd0 : 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E := by linarith
  unfold _root_.GlobalTheory.LevGeo.multBd
  rw [Real.log_pow]
  push_cast
  calc (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * (r : ℝ) ^ 2) *
        Real.log (1 + 2 * (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * r) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E / ε)
      ≤ (2 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * (r : ℝ) ^ 2) *
          Real.log (16 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E * B) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hpos hX) (by positivity)
    _ = _ := by
      rw [Real.log_mul (by positivity) hB0.ne', Real.log_mul (by positivity) hd0.ne',
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_pow]
      push_cast
      ring

end GlobalTheory.SupConstSize

namespace GlobalTheory.SupConstSize
open Real

open NumberField MeasureTheory in
open scoped ENNReal in
open Real in

theorem _root_.GlobalTheory.SupConstSize.chart_factor_size (E : Type) [Field E] [NumberField E] (r : ℕ) (w L : ℝ)
    (hf : 1 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ)) (hr : 2 ≤ r) (hw : 1 ≤ w) (hL : 1 ≤ L)
    (hfr : Real.log (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) + Real.log r ≤ L) (hlw : Real.log w ≤ 2 * L) :
    1 ≤ 8 * ((_root_.GlobalTheory.LevGeo.dimFl E r).factorial : ℝ) /
        (Real.pi * _root_.GlobalTheory.LevGeo.chartRad E r w ^ 2) ^ _root_.GlobalTheory.LevGeo.dimFl E r ∧
    Real.log (8 * ((_root_.GlobalTheory.LevGeo.dimFl E r).factorial : ℝ) /
        (Real.pi * _root_.GlobalTheory.LevGeo.chartRad E r w ^ 2) ^ _root_.GlobalTheory.LevGeo.dimFl E r) ≤
      3 * Real.log 2 + (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * (r : ℝ) ^ 2 / 2 * (12 * L + 16 * Real.log 2) := by
  have hfN : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by exact_mod_cast hf
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ : _root_.GlobalTheory.LevGeo.chartRad E r w = 1 / (200 * (r : ℝ) ^ 3 * (w + _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E)) := by
    unfold _root_.GlobalTheory.LevGeo.chartRad
    rfl
  have hnN : _root_.GlobalTheory.LevGeo.dimFl E r = _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E * (r * (r - 1) / 2) := by
    unfold _root_.GlobalTheory.LevGeo.dimFl
    rfl
  have hn1 : 1 ≤ _root_.GlobalTheory.LevGeo.dimFl E r := by
    rw [hnN]
    have h2 : 2 * 1 ≤ r * (r - 1) := Nat.mul_le_mul hr (by omega)
    have h3 : 1 ≤ r * (r - 1) / 2 := (Nat.le_div_iff_mul_le two_pos).2 (by omega)
    exact one_le_mul_of_one_le_of_one_le hfN h3
  have hnle : (_root_.GlobalTheory.LevGeo.dimFl E r : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) * (r : ℝ) ^ 2 / 2 := by
    rw [hnN, Nat.cast_mul, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Nat.cast_div_le.trans ?_
    have : ((r * (r - 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by
      rw [sq]
      exact_mod_cast Nat.mul_le_mul_left r (Nat.sub_le r 1)
    push_cast at this ⊢
    linarith
  generalize _root_.GlobalTheory.LevGeo.dimFl E r = n at hn1 hnle ⊢
  rw [hρ]
  set f : ℝ := (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E : ℝ) with hfdef
  have hf0 : 0 < f := by linarith
  have hr0 : 0 < (r : ℝ) := by linarith
  have hw0 : 0 < w := by linarith
  set u : ℝ := 200 * (r : ℝ) ^ 3 * (w + f) with hu
  have hu4 : 4 ≤ u := by
    have : 1 ≤ (r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have : 2 ≤ w + f := by linarith
    nlinarith
  have hu0 : 0 < u := by linarith
  have hq : Real.pi * (1 / u) ^ 2 = Real.pi / u ^ 2 := by
    rw [div_pow, one_pow, mul_one_div]
  rw [hq]
  have hqpos : 0 < Real.pi / u ^ 2 := div_pos Real.pi_pos (by positivity)
  have hq1 : Real.pi / u ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_lt_four]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (pow_pos hqpos n), one_mul]
    calc (Real.pi / u ^ 2) ^ n ≤ 1 := pow_le_one₀ hqpos.le hq1
      _ ≤ 8 * (n.factorial : ℝ) := by linarith
  · have hY : 8 * (n.factorial : ℝ) / (Real.pi / u ^ 2) ^ n ≤ 8 * ((n : ℝ) / (Real.pi / u ^ 2)) ^ n := by
      rw [div_pow (n : ℝ) (Real.pi / u ^ 2) n, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (by positivity)
      exact_mod_cast Nat.factorial_le_pow n
    have hwf : w + f ≤ 2 * w * f := by nlinarith [mul_nonneg (sub_nonneg.2 hw) (sub_nonneg.2 hf)]
    have hratio : (n : ℝ) / (Real.pi / u ^ 2) ≤ 2 ^ 16 * (f * r) ^ 8 * w ^ 2 := by
      rw [div_div_eq_mul_div, div_le_iff₀ Real.pi_pos]
      have hule : u ≤ 200 * (r : ℝ) ^ 3 * (2 * w * f) := mul_le_mul_of_nonneg_left hwf (by positivity)
      have h1 : (n : ℝ) * u ^ 2 ≤ f * (r : ℝ) ^ 2 / 2 * (200 * (r : ℝ) ^ 3 * (2 * w * f)) ^ 2 :=
        mul_le_mul hnle (pow_le_pow_left₀ hu0.le hule 2) (by positivity) (by positivity)
      have h38 : f ^ 3 ≤ f ^ 8 := pow_le_pow_right₀ hf (by norm_num)
      have h2 : 80000 * f ^ 3 ≤ 2 ^ 16 * Real.pi * f ^ 8 := by
        have : (80000 : ℝ) ≤ 2 ^ 16 * Real.pi := by nlinarith [Real.pi_gt_three]
        nlinarith [pow_pos hf0 8]
      calc (n : ℝ) * u ^ 2 ≤ f * (r : ℝ) ^ 2 / 2 * (200 * (r : ℝ) ^ 3 * (2 * w * f)) ^ 2 := h1
        _ = ((r : ℝ) ^ 8 * w ^ 2) * (80000 * f ^ 3) := by ring
        _ ≤ ((r : ℝ) ^ 8 * w ^ 2) * (2 ^ 16 * Real.pi * f ^ 8) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 ^ 16 * (f * r) ^ 8 * w ^ 2 * Real.pi := by ring
    have hratio0 : 0 < (n : ℝ) / (Real.pi / u ^ 2) := div_pos (by linarith) hqpos
    have hlog : Real.log ((n : ℝ) / (Real.pi / u ^ 2)) ≤ 12 * L + 16 * Real.log 2 := by
      refine (Real.log_le_log hratio0 hratio).trans ?_
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul hf0.ne' hr0.ne']
      push_cast
      linarith
    have hC : 0 ≤ 12 * L + 16 * Real.log 2 := by
      have := Real.log_pos one_lt_two
      linarith
    calc Real.log (8 * (n.factorial : ℝ) / (Real.pi / u ^ 2) ^ n)
        ≤ Real.log (8 * ((n : ℝ) / (Real.pi / u ^ 2)) ^ n) := Real.log_le_log (by positivity) hY
      _ = 3 * Real.log 2 + n * Real.log ((n : ℝ) / (Real.pi / u ^ 2)) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
            show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          push_cast
          ring
      _ ≤ 3 * Real.log 2 + n * (12 * L + 16 * Real.log 2) := by
          gcongr
      _ ≤ 3 * Real.log 2 + f * (r : ℝ) ^ 2 / 2 * (12 * L + 16 * Real.log 2) := by
          gcongr

end GlobalTheory.SupConstSize

namespace GlobalTheory.SupConstSize
end GlobalTheory.SupConstSize
