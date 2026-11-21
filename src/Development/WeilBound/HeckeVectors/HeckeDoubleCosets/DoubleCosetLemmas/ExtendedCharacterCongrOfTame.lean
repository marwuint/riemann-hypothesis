import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def IntM {a b : Type} (X : Matrix a b (Cv v)) : Prop := ∀ i j, Valued.v (X i j) ≤ 1

def SmM {a b : Type} (X : Matrix a b (Cv v)) : Prop := ∀ i j, Valued.v (X i j) < 1

section Ent

variable {a b c : Type} [Fintype b] {X : Matrix a b (Cv v)} {Y : Matrix b c (Cv v)}

theorem IntM.mul (hX : IntM X) (hY : IntM Y) : IntM (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [map_mul]; exact mul_le_one' (hX i k) (hY k j)

theorem SmM.mul_int (hX : SmM X) (hY : IntM Y) : SmM (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun k _ => by
    rw [map_mul]; exact (mul_le_of_le_one_right' (hY k j)).trans_lt (hX i k)

theorem IntM.mul_sm (hX : IntM X) (hY : SmM Y) : SmM (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun k _ => by
    rw [map_mul]; exact (mul_le_of_le_one_left' (hX i k)).trans_lt (hY k j)

omit [Fintype b] in
theorem SmM.add {X' : Matrix a b (Cv v)} (hX : SmM X) (hX' : SmM X') : SmM (X + X') :=
  fun i j => Valuation.map_add_lt _ (hX i j) (hX' i j)

end Ent

theorem prod_congr_lt {ι : Type} (s : Finset ι) (f g : ι → Cv v) (hf : ∀ i, Valued.v (f i) ≤ 1)
    (hg : ∀ i, Valued.v (g i) ≤ 1) (h : ∀ i, Valued.v (f i - g i) < 1) :
    Valued.v (∏ i ∈ s, g i) ≤ 1 ∧ Valued.v (∏ i ∈ s, f i - ∏ i ∈ s, g i) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨by rw [map_mul]; exact mul_le_one' (hg a) ih.1, ?_⟩
    rw [show f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
      f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i by ring]
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact (mul_le_of_le_one_left' (hf a)).trans_lt ih.2
    · exact (mul_le_of_le_one_right' ih.1).trans_lt (h a)

section Det

variable {n : Type} [Fintype n] [DecidableEq n] {X Y : Matrix n n (Cv v)}

theorem v_sign (σ : Equiv.Perm n) : Valued.v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Cv v) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem IntM.det (hX : IntM X) : Valued.v X.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, v_sign, one_mul]
  exact (prod_congr_lt _ _ _ (fun i => hX (σ i) i) (fun i => hX (σ i) i) (by simp)).1

theorem det_congr (hX : IntM X) (hY : IntM Y) (h : SmM (X - Y)) : Valued.v (X.det - Y.det) < 1 := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun σ _ => ?_
  rw [← mul_sub, map_mul, v_sign, one_mul]
  exact (prod_congr_lt _ _ _ (fun i => hX (σ i) i) (fun i => hY (σ i) i) fun i => h (σ i) i).2

end Det

section Blocks

variable {F : Type} [Field F] {r d c e : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F)
  (y : Matrix (Fin (r + c)) (Fin (r + e)) F)

theorem bAA_mul : bAA (x * y) = bAA x * bAA y + bAD x * bDA y := by
  ext i j; simp [bAA, bAD, bDA, Matrix.mul_apply, Fin.sum_univ_add]

theorem bAD_mul : bAD (x * y) = bAA x * bAD y + bAD x * bDD y := by
  ext i j; simp [bAA, bAD, bDD, Matrix.mul_apply, Fin.sum_univ_add]

theorem bDA_mul : bDA (x * y) = bDA x * bAA y + bDD x * bDA y := by
  ext i j; simp [bAA, bDD, bDA, Matrix.mul_apply, Fin.sum_univ_add]

theorem bDD_mul : bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  ext i j; simp [bDD, bAD, bDA, Matrix.mul_apply, Fin.sum_univ_add]

end Blocks

theorem unitCharExtendedByZero_mul {F : Type} [Field F] (δ : Fˣ →* ℂˣ) (x y : F) :
    chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  by_cases hx : x = 0
  · simp [chi0, hx]
  by_cases hy : y = 0
  · simp [chi0, hy]
  simp only [chi0, dif_neg hx, dif_neg hy, dif_neg (mul_ne_zero hx hy), ← Units.val_mul, ← map_mul]
  congr 2
  exact Units.ext rfl

theorem extendedCharacter_congr_of_tame {δ : (Cv v)ˣ →* ℂˣ} (hδ : IsTame v δ) {x y : Cv v} (hy : Valued.v y = 1)
    (h : Valued.v (x - y) < 1) : chi0 δ x = chi0 δ y := by
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  have h1 : Valued.v (x / y - 1) < 1 := by
    rw [div_sub_one hy0, map_div₀, hy, div_one]; exact h
  have h0 : x / y ≠ 0 := fun h0 => by simp [h0] at h1
  have h2 : chi0 δ (x / y) = 1 := by
    rw [chi0, dif_neg h0, hδ.2 (Units.mk0 _ h0) h1, Units.val_one]
  rw [← div_mul_cancel₀ x hy0, unitCharExtendedByZero_mul, h2, one_mul]

variable {r c : ℕ} {J : Subgroup (GL (Fin (r + c)) (Cv v))}

end CompanionTheory.D.Upq.DoubleCosetLemmas

end
