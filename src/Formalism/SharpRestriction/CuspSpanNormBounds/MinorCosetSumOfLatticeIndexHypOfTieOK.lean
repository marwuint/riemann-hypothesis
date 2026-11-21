import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoCosetCount

noncomputable section

namespace Formalism.MainNotions.KTwoCosetCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section G

def ccOf (CH Cl : ℝ) : ℝ := 17 + 4 / Cl + 4 * |CH|

theorem frameExp_le {r l : ℕ} (hl : l ≤ r) : frameExp r l ≤ r * r := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (r + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, r :=
        Finset.sum_le_sum fun a ha => by
          simp only [Finset.mem_Icc] at ha
          omega
    _ = l * r := by simp
    _ ≤ r * r := Nat.mul_le_mul_right r hl

theorem expo_le {x a J R M F Nn : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hJ : 0 ≤ J) (hJR : J ≤ R) (hNn : 0 ≤ Nn) (hNF : Nn ≤ F)
    (hR : 1 ≤ R) (hRM : R ≤ M) (hF : 1 ≤ F) :
    J + (6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R)) * (2 * Nn * J) ≤
      (17 + 4 * x + 4 * a) * M ^ 2 * F * ((17 + 4 * x + 4 * a) * R) := by
  have hR0 : 0 ≤ R := by linarith
  have hM1 : 1 ≤ M := le_trans hR hRM
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hRM2 : R ≤ M ^ 2 := by nlinarith
  have hc : 1 ≤ 17 + 4 * x + 4 * a := by linarith
  have hA : 6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R) ≤ (8 + 2 * x + 2 * a) * M ^ 2 := by
    have h1 : R * R ≤ M ^ 2 := by nlinarith
    have h3 : a * M * R ≤ a * M ^ 2 := by
      have h5 : M * R ≤ M ^ 2 := by nlinarith
      nlinarith
    have h4 : (1 : ℝ) ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hx]
  have hB : 2 * Nn * J ≤ 2 * F * R := by nlinarith
  have hApos : 0 ≤ 6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R) := by
    have h1 : 0 ≤ x * (2 * (R * R)) := mul_nonneg hx (by nlinarith)
    have h2 : 0 ≤ (1 + a * M) * (2 * R) := mul_nonneg (by nlinarith) (by linarith)
    linarith
  have hstep : (6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R)) * (2 * Nn * J) ≤
      (8 + 2 * x + 2 * a) * M ^ 2 * (2 * F * R) :=
    mul_le_mul hA hB (by nlinarith) (by nlinarith)
  have hMF : 1 ≤ M ^ 2 * F := by nlinarith
  have hJ2 : J ≤ M ^ 2 * F * R := by nlinarith
  have hQ : 0 ≤ (17 + 4 * x + 4 * a) * M ^ 2 * F * R := by
    have : 0 ≤ M ^ 2 * F * R := by nlinarith
    nlinarith
  have hc2 : (17 + 4 * x + 4 * a) * M ^ 2 * F * R ≤
      (17 + 4 * x + 4 * a) * M ^ 2 * F * ((17 + 4 * x + 4 * a) * R) := by
    nlinarith [mul_le_mul_of_nonneg_left hc hQ]
  nlinarith

theorem final_arith {L Cl CH rd : ℝ} {r m f n j : ℕ} (hL : 1 < L) (hCl : 0 < Cl) (hrd1 : 1 ≤ rd)
    (hrdL : Real.log rd ≤ L / Cl) (hr : 1 ≤ r) (hrm : r ≤ m) (hjr : j ≤ r) (hnf : n ≤ f) (hf : 1 ≤ f) :
    (2 : ℝ) ^ j * ((64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r))) ^ (2 * n)) ^ j ≤
      (Real.exp L ^ (ccOf CH Cl * (m : ℝ) ^ 2 * f)) ^ (ccOf CH Cl * (r : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have h2 : (2:ℝ) ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hrdpos : 0 < rd := by linarith
  have hrd : rd ≤ Real.exp (L / Cl) := by
    rw [← Real.exp_log hrdpos]
    exact Real.exp_le_exp.2 hrdL
  have hx : 0 ≤ 1 / Cl := by positivity
  have ha : 0 ≤ |CH| := abs_nonneg _
  have hM : max 1 (2 * Real.exp L ^ (CH * (m:ℝ))) ≤ Real.exp (L * (1 + |CH| * m)) := by
    have e1 : Real.exp L ^ (CH * (m:ℝ)) ≤ Real.exp (L * (|CH| * m)) := by
      rw [← Real.exp_mul]
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_left _ hL0.le
      exact mul_le_mul_of_nonneg_right (le_abs_self CH) (Nat.cast_nonneg m)
    have e2 : (1:ℝ) ≤ Real.exp (L * (|CH| * m)) := Real.one_le_exp (by positivity)
    have e3 : Real.exp (L * (1 + |CH| * m)) = Real.exp L * Real.exp (L * (|CH| * m)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e3]
    apply max_le
    · nlinarith
    · nlinarith
  have hrdp : rd ^ (((2 * (r * r) : ℕ)) : ℝ) ≤ Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) := by
    calc rd ^ (((2 * (r * r) : ℕ)) : ℝ) ≤ (Real.exp (L / Cl)) ^ (((2 * (r * r) : ℕ)) : ℝ) :=
          Real.rpow_le_rpow hrdpos.le hrd (by positivity)
      _ = Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) := by
          rw [← Real.exp_mul]
          congr 1
          push_cast
          ring
  have h64 : (64:ℝ) ≤ Real.exp (L * 6) := by
    rw [show L * 6 = ((6 : ℕ) : ℝ) * L by push_cast; ring, Real.exp_nat_mul]
    calc (64:ℝ) = 2 ^ 6 := by norm_num
      _ ≤ Real.exp L ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
  have hA : 64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r)) ≤
      Real.exp (L * 6) * (Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) * Real.exp (L * (1 + |CH| * m)) ^ (2 * r)) := by
    have hmax0 : 0 ≤ max 1 (2 * Real.exp L ^ (CH * (m : ℝ))) := le_trans zero_le_one (le_max_left _ _)
    gcongr
  have h2j : (2:ℝ) ^ j ≤ Real.exp L ^ j := pow_le_pow_left₀ (by norm_num) h2 j
  have hexpo := expo_le (x := 1 / Cl) (a := |CH|) (J := (j:ℝ)) (R := (r:ℝ)) (M := (m:ℝ)) (F := (f:ℝ)) (Nn := (n:ℝ))
    hx ha (Nat.cast_nonneg j) (by exact_mod_cast hjr) (Nat.cast_nonneg n) (by exact_mod_cast hnf)
    (by exact_mod_cast hr) (by exact_mod_cast hrm) (by exact_mod_cast hf)
  have hcc : ccOf CH Cl = 17 + 4 * (1 / Cl) + 4 * |CH| := by unfold ccOf; ring
  calc (2 : ℝ) ^ j * ((64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r))) ^ (2 * n)) ^ j
      ≤ Real.exp L ^ j * ((Real.exp (L * 6) * (Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) *
          Real.exp (L * (1 + |CH| * m)) ^ (2 * r))) ^ (2 * n)) ^ j := by
        have hA0 : 0 ≤ 64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r)) := by
          have hmax0 : 0 ≤ max 1 (2 * Real.exp L ^ (CH * (m : ℝ))) := le_trans zero_le_one (le_max_left _ _)
          positivity
        have hB := pow_le_pow_left₀ (pow_nonneg hA0 _) (pow_le_pow_left₀ hA0 hA (2 * n)) j
        exact mul_le_mul h2j hB (pow_nonneg (pow_nonneg hA0 _) _) (by positivity)
    _ = Real.exp (L * ((j:ℝ) + (6 + 1 / Cl * (2 * ((r:ℝ) * r)) + (1 + |CH| * m) * (2 * r)) * (2 * n * j))) := by
        simp only [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (L * ((17 + 4 * (1 / Cl) + 4 * |CH|) * (m:ℝ) ^ 2 * f * ((17 + 4 * (1 / Cl) + 4 * |CH|) * r))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hexpo hL0.le)
    _ = (Real.exp L ^ (ccOf CH Cl * (m : ℝ) ^ 2 * f)) ^ (ccOf CH Cl * (r : ℝ)) := by
        rw [← Real.rpow_mul (Real.exp_pos L).le, ← Real.exp_mul, hcc]

end G

end Formalism.MainNotions.KTwoCosetCount

end
