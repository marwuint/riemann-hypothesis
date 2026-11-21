import Formalism.HermitianCurvature.StatementG

open Matrix

namespace Formalism.FourierDecayAlt.P.G6

open Formalism.FourierDecayAlt.G

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem xOf_castSucc {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (k : Fin m) : xOf X B k.castSucc = X k.castSucc k.succ := by
  rw [xOf, Fin.succ_castSucc, blk_cc]

theorem xOf_last {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) :
    xOf X B (Fin.last m) = B (Fin.last m) := by
  rw [xOf, Fin.succ_last, blk_cl]

theorem isStrictUpper_strictUpper {d : ℕ} (v : UT d → ℂ) : IsStrictUpper (strictUpper v) := by
  intro i j h
  simp [strictUpper, not_lt.mpr h]

theorem isStrictUpper_neg {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsStrictUpper X) :
    IsStrictUpper (-X) := by
  intro i j h
  simp [hX i j h]

theorem pow_apply_eq_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsStrictUpper X) (k : ℕ) :
    ∀ i j : Fin d, (j : ℕ) < i + k → (X ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero]
    refine Matrix.one_apply_ne ?_
    intro e
    subst e
    simp at h
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < i + k
    · rw [ih i l hl, zero_mul]
    · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]

theorem pow_apply_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X) :
    ∀ (j : ℕ) (hj : j < m + 1), (X ^ j) 0 ⟨j, hj⟩ =
      ∏ k : Fin j, X ⟨k, by omega⟩ ⟨k + 1, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; simp
  | succ j ih =>
    intro hj
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single (⟨j, by omega⟩ : Fin (m + 1)),
      ih (by omega), Fin.prod_univ_castSucc]
    · rfl
    · intro l _ hl
      by_cases h : (l : ℕ) < j
      · rw [pow_apply_eq_zero hX j 0 l (by simpa using h), zero_mul]
      · have h2 : (l : ℕ) ≠ j := fun e => hl (Fin.ext e)
        rw [hX l ⟨j + 1, hj⟩ (by rw [Fin.le_def]; simp only; omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem pow_mulVec_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) : (X ^ m *ᵥ B) 0 = ∏ k, xOf X B k := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last m), Fin.prod_univ_castSucc, xOf_last]
  · congr 1
    have := pow_apply_zero hX m (Nat.lt_succ_self m)
    rw [show (Fin.last m) = ⟨m, Nat.lt_succ_self m⟩ from rfl, this]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [xOf_castSucc]
    rfl
  · intro l _ hl
    have h2 : (l : ℕ) ≠ m := fun e => hl (Fin.ext e)
    have h3 := l.2
    rw [pow_apply_eq_zero hX m 0 l (by simp only [Fin.val_zero]; omega), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pow_mulVec_succ {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) (k : Fin m) : (X ^ m *ᵥ B) k.succ = 0 := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [pow_apply_eq_zero hX m k.succ l (by have := l.2; simp only [Fin.val_succ]; omega), zero_mul]

theorem sum_mul_zero_pow (m : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range (m + 1), f j * (0 : ℂ) ^ (m - j) = f m := by
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, Nat.sub_self, pow_zero, mul_one, zero_add]
  intro j hj
  have := Finset.mem_range.mp hj
  rw [zero_pow (by omega), mul_zero]

theorem norm_pow_mulVec_le {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {L : ℝ} (hL : 0 ≤ L) (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) (j : ℕ) :
    ∀ i, ‖((-X) ^ j *ᵥ B) i‖ ≤ ((m : ℝ) + 1) ^ j * L ^ (j + 1) := by
  induction j with
  | zero => intro i; simpa using hB i
  | succ j ih =>
    intro i
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
    calc ‖∑ l, (-X) i l * ((-X) ^ j *ᵥ B) l‖ ≤ ∑ l, ‖(-X) i l * ((-X) ^ j *ᵥ B) l‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _l : Fin (m + 1), L * (((m : ℝ) + 1) ^ j * L ^ (j + 1)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul]
          refine mul_le_mul ?_ (ih l) (norm_nonneg _) hL
          simpa using hX i l
      _ = ((m : ℝ) + 1) ^ (j + 1) * L ^ (j + 1 + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

theorem remainder_norm_le_strict_upper {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {ρ' : Fin m → ℂ} {t : ℂ} {L : ℝ} (hL : 1 ≤ L) (ht : ‖t‖ ≤ 1) (hS : IsStrictUpper X)
    (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) (hρ : ∀ k, ‖ρ' k‖ ≤ L) :
    ‖R0 X B ρ' t‖ ≤ (((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m)) * (L ^ (m + 2) * ‖t‖) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have term : ∀ j ∈ Finset.range (m + 1),
      ‖(∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)‖ ≤
        ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 2) * ‖t‖) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hjm : j = m
    · subst hjm
      rw [Finset.sum_eq_zero, zero_mul, norm_zero]
      · positivity
      · intro k _
        rw [pow_mulVec_succ (isStrictUpper_neg hS), mul_zero]
    · have hlt : j < m := by omega
      rw [norm_mul, norm_pow]
      have h1 : ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ ≤
          (m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2) := by
        calc ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖
            ≤ ∑ k : Fin m, ‖ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ := norm_sum_le _ _
          _ ≤ ∑ _k : Fin m, L * (((m : ℝ) + 1) ^ j * L ^ (j + 1)) := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [norm_mul]
              exact mul_le_mul (hρ k) (norm_pow_mulVec_le hL0 hX hB j k.succ) (norm_nonneg _) hL0
          _ = (m : ℝ) * (((m : ℝ) + 1) ^ j * L ^ (j + 2)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
          _ ≤ (m : ℝ) * (((m : ℝ) + 1) ^ m * L ^ (m + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
              refine mul_le_mul (pow_le_pow_right₀ hm1 hlt.le) (pow_le_pow_right₀ hL (by omega))
                (by positivity) (by positivity)
          _ = (m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2) := by ring
      have h2 : ‖t‖ ^ (m - j) ≤ ‖t‖ := pow_le_of_le_one (norm_nonneg _) ht (by omega)
      calc ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ * ‖t‖ ^ (m - j)
          ≤ ((m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2)) * ‖t‖ :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
  calc ‖R0 X B ρ' t‖ ≤ ∑ j ∈ Finset.range (m + 1),
        ‖(∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 2) * ‖t‖) :=
        Finset.sum_le_sum term
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem rpow_bound (m : ℕ) {T ε : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) : (T ^ (-ε)) ^ (m + 2) * T ≤ Real.sqrt T := by
  have hm : (0 : ℝ) < 2 * ((m : ℝ) + 2) := by positivity
  have h1 : ε * (2 * ((m : ℝ) + 2)) ≤ 1 := (le_div_iff₀ hm).mp hε
  have e : (T ^ (-ε)) ^ (m + 2) * T = T ^ (-ε * ((m : ℝ) + 2) + 1) := by
    rw [Real.rpow_add hT, Real.rpow_one, Real.rpow_mul hT.le, ← Real.rpow_natCast]
    push_cast
    rfl
  rw [e, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by nlinarith)

end Formalism.FourierDecayAlt.P.G6

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6

theorem leading_cofactor : Formalism.FourierDecayAlt.G.CofLead := by
  intro m X B ρ' hX
  constructor
  · rw [Cof, sum_mul_zero_pow m (fun j => ((-X) ^ j *ᵥ B) 0)]
    have e : (-X) ^ m = ((-1 : ℂ) ^ m) • X ^ m := by
      rw [← smul_pow, neg_one_smul]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, pow_mulVec_zero hX, smul_eq_mul]
  · rw [R0, sum_mul_zero_pow m (fun j => ∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pow_mulVec_succ (isStrictUpper_neg hX), mul_zero]

end Formalism.FourierDecayAlt.P
