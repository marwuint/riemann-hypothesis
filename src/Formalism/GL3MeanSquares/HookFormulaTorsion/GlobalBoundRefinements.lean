import Mathlib
import Formalism.GL3MeanSquares.InvNormSqConjRatioPowIdentities
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
import Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.GlobalBoundRefinements

section ShortIntervalLowerBound

open Formalism.HermitianLattices.GL2PrimeSums

open private gl2a4_root gl2a4_rho_pos gl2a4_rho_mono gl2a4_weight gl2a4_E_lower gl2a4_E_upper Li_le_three_mul_div_log
  gl2a4_Li_two gl2a4_Li_mono gl2a4_E_four gl2a4_E_nonneg Emain_lower_bound from Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound

private lemma exists_adjusted_exceptional_exponent {cb B β X : ℝ} {θ : ℤ} (hcb : 0 < cb) (hB : 4 ≤ B)
    (hβ : θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β)
    (hcbX : 2 / cb * Real.log B ≤ Real.log X) :
    ∃ β' : ℝ, 1 / 2 ≤ β' ∧ β' < 1 ∧
      (∀ Y, Emain θ β Y = Emain θ β' Y) ∧ (θ = 1 → 2 / B ^ 2 ≤ (1 - β') * Real.log X) := by
  by_cases hθ : θ = 0
  · refine ⟨1 / 2, by norm_num, by norm_num, fun Y => ?_, fun h1 => ?_⟩
    · simp only [Emain, hθ, Int.cast_zero, zero_mul, sub_zero]
    · exfalso
      omega
  · obtain ⟨h1, h2, h3⟩ := hβ hθ
    refine ⟨β, h1, h2, fun Y => rfl, fun _ => ?_⟩
    have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
    have hBpos : 0 < B := by linarith
    have hcbne : cb ≠ 0 := hcb.ne'
    have hlogne : Real.log B ≠ 0 := hlogB.ne'
    have hBne : B ≠ 0 := hBpos.ne'
    have e : 2 / B ^ 2 = cb / (B ^ 2 * Real.log B) * (2 / cb * Real.log B) := by
      field_simp
      try ring
    rw [e]
    exact mul_le_mul h3 hcbX (mul_nonneg (div_nonneg (by norm_num) hcb.le) hlogB.le) (by linarith)

private lemma mul_log_le_log_of_rpow_le {B K X : ℝ} (hB : 4 ≤ B) (h : B ^ K ≤ X) : K * Real.log B ≤ Real.log X := by
  have hB0 : 0 < B := by linarith
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hB0 K) h
  rwa [Real.log_rpow hB0] at h1

set_option maxHeartbeats 1000000 in
private lemma exceptional_zero_contribution_bound {Cr cr B G β X : ℝ} {θ : ℤ} {π₁ π₂ : ℝ → ℕ} {η' : ℝ → ℝ} (hCr : 0 < Cr) (hcr : 0 < cr)
    (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) (hB : 4 ≤ B) (hG1 : 1 ≤ G) (hGB : G ≤ B)
    (hβ1 : 1 / 2 ≤ β) (hβ2 : β < 1) (hd : θ = 1 → 2 / B ^ 2 ≤ (1 - β) * Real.log X)
    (hX : B ^ (60 : ℝ) ≤ X)
    (hπ₂ : ∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y)
    (hη : ∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log B)
    (hQ : ∀ Y : ℝ, X ≤ Y →
      |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y)
    {h : ℝ} (hh1 : h ≤ 1) (hρ : rhoErr Cr cr B X ≤ h / 100) (hB7 : B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3)) :
    1 / 100 * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X := by
  obtain ⟨u, hu, hu12, hsq, hcb, hlogu⟩ := gl2a4_root hB hX
  have hB0 : 0 < B := by linarith
  have hu0 : 0 < u := by linarith
  have hX0 : 0 < X := by rw [← hu12]; positivity
  have hXu : u ≤ X := by
    have : u ^ 1 ≤ u ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith [pow_one u]
  have hXbig : 1296 ≤ X := by
    have h2 : u ^ 2 ≤ u ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hh0 : 0 < h := by linarith [gl2a4_rho_pos (c := cr) (B := B) (X := X) hCr]
  set X' := X * (1 + h) with hX'
  have hXX' : X ≤ X' := by rw [hX']; nlinarith
  have hX'2 : X' ≤ 2 * X := by rw [hX']; nlinarith
  have hX'sq : X' ≤ X ^ 2 := by nlinarith
  have hX'0 : 0 < X' := by linarith
  obtain ⟨W, hW1, hW2, hWlo, hWhi⟩ := gl2a4_weight hθ hβ2 (B := B) (Z := X) (by linarith) (by linarith)
    (by
      intro h
      have h1 := hd h
      have e : 2 / B ^ 2 = 2 * (1 / B ^ 2) := by ring
      have : 0 < 1 / B ^ 2 := by positivity
      rw [e] at h1
      linarith)
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW1
  have hLL' : Real.log X ≤ Real.log X' := Real.log_le_log hX0 hXX'
  have hL'0 : 0 < Real.log X' := by linarith
  have hL' : Real.log X' ≤ 2 * Real.log X := by
    have h1 : Real.log X' ≤ Real.log (X ^ 2) := Real.log_le_log hX'0 hX'sq
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  set L := Real.log X with hLdef
  set T := W * h * X / L with hT
  have hT0 : 0 < T := by rw [hT]; positivity

  have a1 := gl2a4_E_lower θ (β := β) (a := X) (b := X') (W := W) (by linarith) hX1 hXX' hW0.le
    (fun t ht _ => hWlo t ht)
  have a2 : T / 2 ≤ W * (X' - X) / Real.log X' := by
    have e1 : X' - X = h * X := by rw [hX']; ring
    have e2 : T / 2 = W * (h * X) / (2 * L) := by rw [hT]; field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by positivity) hL'0 hL'

  have b1 := gl2a4_E_upper θ (β := β) (a := 4) (b := X') (V := 2 * W) (by linarith) (by norm_num)
    (by linarith) (fun t ht1 ht2 => hWhi t (by linarith) (by linarith))
  have b2 : Li X' ≤ 3 * X' / Real.log X' := Li_le_three_mul_div_log (by linarith)
  have b3 : 3 * X' / Real.log X' ≤ 6 * X / L := by
    calc 3 * X' / Real.log X' ≤ 6 * X / Real.log X' :=
          div_le_div_of_nonneg_right (by linarith) hL'0.le
      _ ≤ 6 * X / L := div_le_div_of_nonneg_left (by positivity) hL hLL'
  have b4 : 0 ≤ Li 4 := by
    rw [← gl2a4_Li_two]; exact gl2a4_Li_mono (by norm_num) (by norm_num)
  have b5 : Emain θ β X' ≤ 6 + 12 * (W * X / L) := by
    have h1 : 2 * W * (Li X' - Li 4) ≤ 2 * W * (6 * X / L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e : 2 * W * (6 * X / L) = 12 * (W * X / L) := by ring
    have := (gl2a4_E_four hθ hβ1 hβ2).2
    linarith
  have b6 : h * Emain θ β X' ≤ 6 * h + 12 * T := by
    have h1 := mul_le_mul_of_nonneg_left b5 hh0.le
    have e : h * (6 + 12 * (W * X / L)) = 6 * h + 12 * T := by rw [hT]; ring
    linarith
  have hE0 : 0 ≤ Emain θ β X := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith)
  have hE'0 : 0 ≤ Emain θ β X' := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith)
  have hEE : Emain θ β X ≤ Emain θ β X' := by linarith

  have q1 := (abs_le.1 (hQ X' hXX')).1
  have q2 := (abs_le.1 (hQ X le_rfl)).2
  have r1 : rhoErr Cr cr B X' * Emain θ β X' ≤ h / 100 * Emain θ β X' :=
    mul_le_mul_of_nonneg_right
      (le_trans (gl2a4_rho_mono hCr hcr (by linarith) hX1.le hXX') hρ) hE'0
  have r2 : rhoErr Cr cr B X * Emain θ β X ≤ h / 100 * Emain θ β X' :=
    mul_le_mul hρ hEE hE0 (by positivity)
  have s1 : Real.sqrt X' ≤ 3 / 2 * u ^ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (3 / 2 * u ^ 6) ^ 2 = 9 / 4 * X := by rw [← hu12]; ring
    rw [this]; linarith
  have s2 : G * (π₂ X' : ℝ) ≤ 3 * B * u ^ 6 := by
    have h1 : (π₂ X' : ℝ) ≤ 3 * u ^ 6 := by linarith [hπ₂ X' (by linarith)]
    calc G * (π₂ X' : ℝ) ≤ B * (3 * u ^ 6) := mul_le_mul hGB h1 (Nat.cast_nonneg _) hB0.le
      _ = 3 * B * u ^ 6 := by ring
  have s3 : 0 ≤ G * (π₂ X : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hlBu : 3 * Real.log B ≤ u := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hB0 _) hX
    rw [Real.log_rpow hB0] at h1
    linarith
  have s4 : G * η' X' ≤ B * u :=
    mul_le_mul hGB (le_trans (hη X').2 hlBu) (hη X').1 hB0.le
  have s5 : 0 ≤ G * η' X := mul_nonneg (by linarith) (hη X).1

  have hB7' : B ^ 7 ≤ h * u ^ 4 := by
    rw [← hcb, ← Real.rpow_ofNat]; exact hB7
  have f1 : B ^ 3 ≤ h * u ^ 4 :=
    le_trans (pow_le_pow_right₀ (by linarith) (by norm_num)) hB7'
  have f2 : 800 * B ^ 3 ≤ h * u ^ 5 := by
    have h1 : B ^ 3 * 800 ≤ h * u ^ 4 * u := mul_le_mul f1 (by linarith) (by norm_num) (by positivity)
    have e : h * u ^ 4 * u = h * u ^ 5 := by ring
    linarith
  have f3 : 8 * B ^ 3 * u ^ 6 * L ≤ 12 / 100 * h * u ^ 12 := by
    calc 8 * B ^ 3 * u ^ 6 * L ≤ 8 * B ^ 3 * u ^ 6 * (12 * u) :=
          mul_le_mul_of_nonneg_left hlogu (by positivity)
      _ = 12 / 100 * (800 * B ^ 3) * u ^ 7 := by ring
      _ ≤ 12 / 100 * (h * u ^ 5) * u ^ 7 := by gcongr
      _ = 12 / 100 * h * u ^ 12 := by ring
  have f5 : 1 / (2 * B ^ 2) * (h * X / L) ≤ T := by
    have e : T = W * (h * X / L) := by rw [hT]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hW1 (by positivity)
  have f4 : 4 * B * u ^ 6 ≤ 12 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) := by
    have e : 12 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) = 12 / 100 * h * u ^ 12 / (2 * B ^ 2 * L) := by
      rw [← hu12]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 4 * B * u ^ 6 * (2 * B ^ 2 * L) = 8 * B ^ 3 * u ^ 6 * L := by ring
    rw [e2]; exact f3
  have f6 : 12 / 100 * h + B * u ≤ B * u ^ 6 := by
    have h5 : u ^ 1 ≤ u ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [pow_one] at h5
    have h6 : u * 2 ≤ u * u ^ 5 := mul_le_mul_of_nonneg_left (by linarith) hu0.le
    have e6 : u * u ^ 5 = u ^ 6 := by ring
    rw [e6] at h6
    have h7 : B * (u * 2) ≤ B * u ^ 6 := mul_le_mul_of_nonneg_left h6 hB0.le
    have h8 : (1 : ℝ) * 1 ≤ B * u := mul_le_mul (by linarith) (by linarith) (by norm_num) hB0.le
    linarith

  set Δ := (π₁ X' : ℝ) - π₁ X with hΔ
  have m1 : 14 / 100 * T ≤ G * Δ := by
    have e : G * Δ = G * ((π₁ X' : ℝ) + π₂ X' + η' X') - G * ((π₁ X : ℝ) + π₂ X + η' X) - G * (π₂ X' : ℝ)
        + G * (π₂ X : ℝ) - G * η' X' + G * η' X := by rw [hΔ]; ring
    rw [e]
    linarith only [q1, q2, r1, r2, s2, s3, s4, s5, a1, a2, b6, f4, f5, f6]
  have hΔ0 : 0 ≤ Δ := by
    by_contra hneg0
    have hneg := not_le.1 hneg0
    have : G * Δ < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  have m2 : G * Δ ≤ B * Δ := mul_le_mul_of_nonneg_right hGB hΔ0
  have hR0 : 0 < h * X / L := by positivity
  have m3 : 7 / 100 * (1 / B ^ 3) * (h * X / L) ≤ Δ := by
    have h1 : 14 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) ≤ B * Δ := by linarith
    have e : 7 / 100 * (1 / B ^ 3) * (h * X / L) = 14 / 100 * (1 / (2 * B ^ 2) * (h * X / L)) / B := by
      field_simp; ring
    rw [e, div_le_iff₀ hB0]
    linarith
  have a4 : B ^ (-6 : ℝ) ≤ 1 / B ^ 3 := by
    have h1 : B ^ (-6 : ℝ) ≤ B ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : B ^ (-3 : ℝ) = 1 / B ^ 3 := by
      rw [Real.rpow_neg hB0.le, Real.rpow_ofNat, one_div]
    linarith
  have m4 : 1 / 100 * h * B ^ (-6 : ℝ) * X / L ≤ 7 / 100 * (1 / B ^ 3) * (h * X / L) := by
    have e : 1 / 100 * h * B ^ (-6 : ℝ) * X / L = 1 / 100 * B ^ (-6 : ℝ) * (h * X / L) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hR0.le
    have : 0 < 1 / B ^ 3 := by positivity
    linarith
  linarith

theorem shortIntervalLowerBound : ShortIntervalLowerBound := by
  intro C₀ Cr cr cb hC₀ hCr hcr hcb
  obtain ⟨Cm, hC0m, hC60, hCcb⟩ : ∃ Cm : ℝ, C₀ ≤ Cm ∧ 60 ≤ Cm ∧ 2 / cb ≤ Cm :=
    ⟨max C₀ (max 60 (2 / cb)), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  refine ⟨Cm, 1 / 100, hC0m, by norm_num, ?_⟩
  intro B G β θ π₁ π₂ η' hB hG1 hGB hθ hβ hπ₂ hη hQ X hX
  have hθ' : θ = -1 ∨ θ = 0 ∨ θ = 1 := by simpa using hθ
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hK := mul_log_le_log_of_rpow_le hB hX
  have hX60 : B ^ (60 : ℝ) ≤ X := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC60) hX
  have hXC₀ : B ^ C₀ ≤ X := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC0m) hX
  have hcbX : 2 / cb * Real.log B ≤ Real.log X :=
    le_trans (mul_le_mul_of_nonneg_right hCcb hlogB.le) hK
  obtain ⟨β', hβ1, hβ2, hE, hd⟩ := exists_adjusted_exceptional_exponent hcb hB hβ hcbX
  have hlow := Emain_lower_bound hθ' hB hβ1 hβ2 hd hX60
  refine ⟨?_, ?_⟩
  · rw [hE X]
    exact hlow
  · intro h hh1 hρ hB7
    refine exceptional_zero_contribution_bound hCr hcr hθ' hB hG1 hGB hβ1 hβ2 hd hX60 hπ₂ hη ?_ hh1 hρ hB7
    intro Y hY
    rw [← hE Y]
    exact hQ Y (le_trans hXC₀ hY)

theorem shortIntervalImpliesProgressions_statement : ShortIntervalImpliesProgressions := by
  intro hL C₀ Cr cr cb hC₀ hCr hcr hcb hQ
  obtain ⟨C₀', c, hC₀', hc, H⟩ := hL C₀ Cr cr cb hC₀ hCr hcr hcb
  refine ⟨C₀', c, lt_of_lt_of_le hC₀ hC₀', hc, ?_⟩
  intro m a hm ha Y h hY hh1 hρ h7
  obtain ⟨θ, β, η', hθ, hβ, hη, happrox⟩ := hQ m a hm ha
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : (4 : ℝ) ≤ 4 * m := by linarith
  have htot0 : 0 < m.totient := by
    first
    | exact Nat.totient_pos.mpr (by omega)
    | exact Nat.totient_pos (by omega)
  have htot1 : (1 : ℝ) ≤ (m.totient : ℝ) := by exact_mod_cast htot0
  have htotB : (m.totient : ℝ) ≤ 4 * m := by
    have h1 : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    linarith
  have key := (H (4 * m) (m.totient : ℝ) β θ
    (fun Z => ((Icc 1 ⌊Z⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card) (fun _ => 0) η'
    hB htot1 htotB hθ hβ
    (fun Z _ => by
      show ((0 : ℕ) : ℝ) ≤ 2 * Real.sqrt Z
      rw [Nat.cast_zero]
      positivity)
    hη
    (fun Z hZ => by
      have hz := happrox Z hZ
      show |(m.totient : ℝ) * ((((Icc 1 ⌊Z⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ)
        + ((0 : ℕ) : ℝ) + η' Z) - Emain θ β Z| ≤ rhoErr Cr cr (4 * m) Z * Emain θ β Z
      rw [Nat.cast_zero, add_zero]
      exact hz)
    Y hY).2 h hh1 hρ h7
  have hY1 : (1 : ℝ) ≤ Y := by
    have h41 : (1 : ℝ) ≤ 4 * m := by linarith
    have := Real.one_le_rpow h41 (le_trans hC₀.le hC₀')
    linarith
  have hYpos : 0 < Y := by linarith
  have hY13 : 0 ≤ Y ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hYpos.le _
  have h47 : 0 < (4 * (m : ℝ)) ^ (7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpos : 0 < h := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hfl1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY1)
  have hfl2 : ⌊Y⌋₊ ≤ ⌊Y * (1 + h)⌋₊ := Nat.floor_mono (by nlinarith)
  have hunion : Icc 1 ⌊Y * (1 + h)⌋₊ = Icc 1 ⌊Y⌋₊ ∪ Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint ((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a))
      ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_filter, Finset.mem_Icc] at hx1
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx2
    omega
  have hcard : ((Icc 1 ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card
      = ((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card
        + ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card := by
    rw [hunion, Finset.filter_union]
    first
    | exact Finset.card_union_of_disjoint hdisj
    | exact Finset.card_disjoint_union hdisj
    | exact Finset.card_union_eq_card_add_card.mpr hdisj
  have key2 : c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Icc 1 ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ)
        - (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ) := key
  rw [hcard, Nat.cast_add] at key2
  linarith

end ShortIntervalLowerBound

section T2

open NumberField
open Formalism.LogVandermondeBounds.StandardLattice

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

theorem log_l_value_field_bound : LogLFunctionEulerBound := by
  intro K _ _ _ hK M hM
  have hpos : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
    fun P => (euler_factor_log_bound K hK M (by omega) P.1 P.2).1
  have hpart := partial_sums_log_euler_factor_le K hK M hM
  have habs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) hpart
  have hsum : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := habs.of_abs
  have hprod : Real.exp (∑' P : {P : Ideal (𝓞 K) // P.IsMaximal},
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) = Formalism.HermitianLatticesTheory.lValEta K M :=
    Real.rexp_tsum_eq_tprod hpos hsum
  refine ⟨Real.multipliable_of_summable_log hpos hsum, ?_, ?_⟩
  · rw [← hprod]; exact Real.exp_pos _
  · rw [← hprod, Real.log_exp]
    calc |∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
        ≤ ∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun P :
            {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1))
            (by simpa [Real.norm_eq_abs] using habs)
      _ ≤ _ := habs.tsum_le_of_sum_le hpart

end T2

end Formalism.HermitianLattices.GlobalBoundRefinements
