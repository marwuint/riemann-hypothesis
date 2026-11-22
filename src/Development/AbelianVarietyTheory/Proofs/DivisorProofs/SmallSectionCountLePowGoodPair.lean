import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N 0 R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f :=
    fun a c σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hpH, hpn⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (-1) b t htH N
  have e1 : (N : ℤ) + N * -1 = 0 := by ring
  have e2 : (0 : ℤ) + N * b = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N 0 R, f * t ^ N ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH, hn⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P N 0 (N * -1) (N * b) f (t ^ N) hfH hpH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hpn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    exact (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
  have hinj : Set.InjOn (fun f => f * t ^ N) (P.Bl N 0 R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) h
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N 0 R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hX P b s t hG
  have hRep : P.Rep 0 (b : ℤ) (P.A.pow b) := by
    have := _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 0 1 P.A b (_root_.GlobalTheory.VolBr.Pair.rep_base k X p P).2.1
    simpa using this
  have hnef : (P.A.pow b).IsNef D := _root_.GlobalTheory.NefPow.isNef_pow hAC k X p D hX P.A b hG.nef
  have hnef0 : ((P.A.pow b).shift (fun _ => (0 : ℝ)) fun _ => rfl).IsNef D :=
    _root_.GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX (P.A.pow b) 0 le_rfl hnef
  obtain ⟨Φ, hΦ⟩ := ((hAC.arExists k X p D hX).2 Unit (fun _ => P.A.pow b)).1
  have hα := ((hAC.arIso k X p D hX).2 Unit (fun _ => P.A.pow b) Φ hΦ).1 ()
  have hlim := _root_.GlobalTheory.VolBr.lc_tendsto_of_rep hHS hAC k X p D hX P 0 b (P.A.pow b) _ 0 hRep hα hnef0 3 (by norm_num)
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      P.lc ((m : ℤ) * 0) ((m : ℤ) * b) (Real.exp (3 * m)) / (m : ℝ) ^ (D + 1) < C :=
    ⟨_, hlim.eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  rw [div_lt_iff₀ hpos] at hN
  simp only [mul_zero] at hN
  refine le_trans ?_ hN.le
  exact lc_le_of_good P hG N _ (_root_.GlobalTheory.VolBr.BallFinite.bl_finite hHS k X p D hX P b s t hG 0 _ _ hAC)

end GlobalTheory.VolBr
