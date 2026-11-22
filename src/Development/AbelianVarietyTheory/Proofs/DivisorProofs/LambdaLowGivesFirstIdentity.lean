import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafIPOfTwoConstants
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.HalfNorm

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.IPbProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_b {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  have hx := L.sc.one_lt_alt
  have h0 : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith) _
  unfold Scale.b
  exact Real.one_le_exp h0

theorem La_le_three {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : L.La ≤ 3 * L.sc.L := by
  obtain ⟨hN, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.n_pos'
    exact_mod_cast this
  have hq : (1 : ℝ) ≤ (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.one_le
  have hd : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.one_le
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hb := one_le_b L
  have hnc : (D.R.n : ℝ) ≤ szCond L := by
    have h := D.host.four_ord_le_condN
    have h' : D.R.n ≤ D.host.QS * D.host.q * D.host.d := by rw [D.R.n_eq_ord]; omega
    unfold szCond; exact_mod_cast h'
  have hc1 : 1 ≤ szCond L := hn.trans hnc
  have hcb : szCond L ≤ L.sc.b := by
    have h1 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
    have h3 : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have h4 : szCond L ^ 36 ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) h2
    have h5 : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hC
    linarith
  have hxn : L.sc.x ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    have he := L.sc.eps_pos
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by unfold szTh; linarith)
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hxb : L.sc.x ≤ L.sc.b := (hxn.trans hnc).trans hcb
  have hrb : D.host.rdE ≤ L.sc.b := (UpperTheory.Ram.Rd.rdE_le_cond D.host).trans hcb
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have l1 := Real.log_le_log (by linarith) hxb
  have l2 := Real.log_le_log (by linarith) hrb
  have hx0 : 0 < L.sc.x := by linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have e : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a Scale.b
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  linarith

end GlobalTheory.BigTop.Fun.IPbProof

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
