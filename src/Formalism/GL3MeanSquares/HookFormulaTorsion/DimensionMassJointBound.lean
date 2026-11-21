import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
import Formalism.LogVandermondeBounds.LogVandermondeProofs.BlockDimensionIdentities

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

private lemma triangular_numbers_half (k : ℕ) : ∃ A, k * (k - 1) / 2 = A ∧ k * (k + 1) / 2 = A + k ∧ k * k = 2 * A + k := by
  have hY : k * (k + 1) / 2 = k * (k - 1) / 2 + k := by
    have e : k * (k + 1) = k * (k - 1) + k * 2 := by
      cases k with
      | zero => simp
      | succ n => rw [Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  refine ⟨k * (k - 1) / 2, rfl, hY, ?_⟩
  have := half_add_half k
  rw [hY] at this
  linarith

private lemma odd_square_expansion (k s : ℕ) :
    (k + 2 * s + 1) ^ 2 = k * k + 4 * (s * k) + 4 * (s * s) + 2 * k + 4 * s + 1 := by
  ring

private lemma exponent_square_identities (k s A : ℕ) (hA : k * k = 2 * A + k) :
    ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 = 2 * (s * k) + s + 2 * (s * s) ∧
    ((k + 2 * s + 1) ^ 2 + 3 * k + 1 + 2 * s) / 2 = A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s) := by
  rw [odd_square_expansion, show (k + 1) ^ 2 = k * k + 2 * k + 1 by ring, hA]
  generalize s * k = X
  generalize s * s = Y
  constructor <;> omega

private lemma card_general_linear_group (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) * ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  rw [cardGeneralLinear F n, ← pow_add, half_add_half]

theorem local_index_formula : LocalColumnIndex := by
  intro F _ _ _ k m hm hme hF
  dsimp only
  have hg3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hg0 : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2]
  obtain ⟨hb1, hb2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 k
  obtain ⟨hc1, hc2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 (k + 2 * s + 1)
  refine ⟨⟨_, hb1, hb2, ?_⟩, ⟨_, hc1, hc2, ?_⟩⟩
  · rw [cardGeneralLinear F k, div_eq_iff (pow_ne_zero _ hg0)]
    ring
  · rw [card_general_linear_group F, (exponent_square_identities k s A hA3).1, (exponent_square_identities k s A hA3).2, hA1]
    have hexp : (k + 2 * s + 1) * (k + 2 * s + 1) = (2 * (s * k) + s + 2 * (s * s)) + A +
        (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) := by
      rw [← sq, odd_square_expansion, hA3]
      ring
    rw [hexp, pow_add, pow_add,
      div_eq_iff (mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hg0))]
    ring

private lemma prod_two_factor_split (f E : ℕ) (G : Fin 2 → ℝ) (t : Fin 2 → ℕ → ℝ) :
    ∏ i, ∏ ρ ∈ range f, G i ^ E * t i ρ =
      (G 0 * G 1) ^ (E * f) * ∏ i, ∏ ρ ∈ range f, t i ρ := by
  simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [mul_pow, pow_mul, pow_mul]

private lemma prod_half_to_one_bounds (f : ℕ) (t : Fin 2 → ℕ → ℝ) (h : ∀ i ρ, 1 / 2 ≤ t i ρ ∧ t i ρ ≤ 1) :
    ((2 : ℝ) ^ (2 * f))⁻¹ ≤ ∏ i, ∏ ρ ∈ range f, t i ρ ∧ ∏ i, ∏ ρ ∈ range f, t i ρ ≤ 1 := by
  have h0 : ∀ i ρ, 0 ≤ t i ρ := fun i ρ => le_trans (by norm_num) (h i ρ).1
  constructor
  · calc ((2 : ℝ) ^ (2 * f))⁻¹ = ∏ i : Fin 2, ∏ ρ ∈ range f, (1 / 2 : ℝ) := by
          simp only [Finset.prod_const, Finset.card_range, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, one_div, inv_pow, mul_comm]
      _ ≤ ∏ i, ∏ ρ ∈ range f, t i ρ :=
          Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun ρ _ => by norm_num)
            (fun i _ => Finset.prod_le_prod (fun ρ _ => by norm_num) (fun ρ _ => (h i ρ).1))
  · exact Finset.prod_le_one (fun i _ => Finset.prod_nonneg fun ρ _ => h0 i ρ)
      (fun i _ => Finset.prod_le_one (fun ρ _ => h0 i ρ) (fun ρ _ => (h i ρ).2))

theorem index_ratio_bound : IndexRatioComparison := by
  intro f k m g₁ g₂ Ipi Isig θ θ' hm hme hg1 hg2 hθ
  dsimp only
  intro hIpi hIsig
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2] at hIsig
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  rw [(exponent_square_identities k s A hA3).2, prod_two_factor_split] at hIsig
  rw [hA2, prod_two_factor_split] at hIpi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hIpi hIsig
  obtain ⟨hPl, hPu⟩ := prod_half_to_one_bounds f θ (fun i ρ => ⟨(hθ i ρ).1, (hθ i ρ).2.1⟩)
  obtain ⟨hQl, hQu⟩ := prod_half_to_one_bounds f θ' (fun i ρ => ⟨(hθ i ρ).2.2.1, (hθ i ρ).2.2.2⟩)
  have hX0 : 0 < g₁ * g₂ := by nlinarith
  have hc : (0 : ℝ) < ((2 : ℝ) ^ (2 * f))⁻¹ := by positivity
  have hPpos : 0 < ∏ i, ∏ ρ ∈ range f, θ i ρ := lt_of_lt_of_le hc hPl
  have hN : (g₁ * g₂) ^ ((f : ℝ) * ((2 * s + 2 : ℕ) : ℝ) * (2 * (k : ℝ) + ((2 * s + 2 : ℕ) : ℝ) - 1) / 2) =
      (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hratio : Isig / Ipi = (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) *
      ((∏ i, ∏ ρ ∈ range f, θ' i ρ) / ∏ i, ∏ ρ ∈ range f, θ i ρ) := by
    rw [hIsig, hIpi]
    have e : (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) * f =
        (A + k) * f + (2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f := by ring
    rw [e, pow_add, mul_assoc, mul_div_mul_left _ _ (pow_pos hX0 _).ne', mul_div_assoc]
  rw [hN, hratio]
  have hXN : 0 ≤ (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) :=
    (pow_pos hX0 _).le
  have h22 : (2 : ℝ) ^ (2 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  constructor
  · rw [mul_comm ((2 : ℝ) ^ (2 * f))⁻¹]
    refine mul_le_mul_of_nonneg_left ?_ hXN
    rw [le_div_iff₀ hPpos]
    nlinarith
  · rw [mul_comm ((2 : ℝ) ^ (2 * f))]
    refine mul_le_mul_of_nonneg_left ?_ hXN
    rw [div_le_iff₀ hPpos]
    nlinarith [mul_le_mul_of_nonneg_left hPl (by positivity : (0 : ℝ) ≤ 2 ^ (2 * f))]

private lemma increments_sum_lower_bound (m : ℕ) (b : ℕ → ℝ) (h₀ : ℝ) (hb : ∀ j, j + 1 < m → h₀ ≤ b (j + 1) - b j)
    (a : ℕ) : ∀ d, a + d < m → (d : ℝ) * h₀ ≤ b (a + d) - b a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := hb (a + d) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

theorem least_noncompact_gap : LeastNoncompactGap := by
  intro k m v b h₀ hk hh hv hb0 hb i j hij hj hsg
  simp only [plusSign, ne_eq, decide_eq_decide] at hsg
  by_cases hi : i < k - 1
  · by_cases hj' : j < k - 1
    · exact absurd ⟨fun _ => Or.inl hj', fun _ => Or.inl hi⟩ hsg
    · have hodd : (j - (k - 1)) % 2 = 1 := by
        by_contra hc
        exact hsg ⟨fun _ => Or.inr (by omega), fun _ => Or.inl hi⟩
      simp only [rowPar, hi, hj', if_true, if_false]
      have hst := increments_sum_lower_bound m b h₀ hb 0 (j - (k - 1)) (by omega)
      simp only [zero_add] at hst
      have h1 : (1 : ℝ) ≤ ((j - (k - 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - (k - 1))
      have := hv i hi
      nlinarith [mul_le_mul_of_nonneg_right h1 hh]
  · have hj' : ¬ j < k - 1 := by omega
    simp only [rowPar, hi, hj', if_false]
    have hst := increments_sum_lower_bound m b h₀ hb (i - (k - 1)) (j - (k - 1) - (i - (k - 1))) (by omega)
    have e : i - (k - 1) + (j - (k - 1) - (i - (k - 1))) = j - (k - 1) := by omega
    rw [e] at hst
    have h1 : (1 : ℝ) ≤ ((j - (k - 1) - (i - (k - 1)) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ j - (k - 1) - (i - (k - 1)))
    nlinarith [mul_le_mul_of_nonneg_right h1 hh]

end Formalism.HermitianLattices.GenusMassVolumes
