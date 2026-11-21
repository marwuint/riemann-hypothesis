import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.PatGrp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

def Supp (Φ : ι → ι → Prop) (N : Matrix ι ι K) : Prop := ∀ i j, N i j ≠ 0 → Φ i j

theorem mem_patSet_iff (h : IsPat Φ) (u : GL ι K) :
    u ∈ patSet K Φ ↔ Supp Φ ((u : Matrix ι ι K) - 1) := by
  unfold patSet
  rw [Set.mem_setOf_eq]
  constructor
  · intro hu i j hN
    by_contra hΦ
    apply hN
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.sub_apply, Matrix.one_apply_eq, (hu i i).1 rfl, sub_self]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, (hu i j).2 hij hΦ, sub_zero]
  · intro hS i j
    refine ⟨fun hij => ?_, fun hij hΦ => ?_⟩
    · subst hij
      have h0 : ((u : Matrix ι ι K) - 1) i i = 0 := by
        by_contra hne
        exact h.1 i (hS i i hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0
    · have h0 : ((u : Matrix ι ι K) - 1) i j = 0 := by
        by_contra hne
        exact hΦ (hS i j hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at h0

theorem Supp.mul (h : IsPat Φ) {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) :
    Supp Φ (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact h.2 i k j (hA i k (left_ne_zero_of_mul hk)) (hB k j (right_ne_zero_of_mul hk))

theorem Supp.add {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) : Supp Φ (A + B) := by
  intro i j hij
  by_cases ha : A i j = 0
  · apply hB
    intro hb
    apply hij
    rw [Matrix.add_apply, ha, hb, add_zero]
  · exact hA i j ha

theorem det_one_add (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by
  classical
  let b : ι → ℕ := fun i => (Finset.univ.filter fun k => Φ k i).card
  have hb : ∀ i j, Φ i j → b i < b j := by
    intro i j hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact h.2 k i j hk hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.1 i
  have hN0 : ∀ i j, b j ≤ b i → N i j = 0 := by
    intro i j hle
    by_contra hne
    exact absurd (hb i j (hN i j hne)) (not_lt.2 hle)
  have hT : (1 + N).BlockTriangular b := by
    intro i j hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblk : (1 + N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩
    have hNij : N i j = 0 := hN0 i j (by rw [hi, hj])
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero,
        Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]
  rw [hblk, Matrix.det_one]

def patSubgroup (h : IsPat Φ) : Subgroup (GL ι K) :=
  let M : Submonoid (GL ι K) :=
    { carrier := patSet K Φ
      mul_mem' := by
        intro u v hu hv
        have hu' := (mem_patSet_iff h u).1 hu
        have hv' := (mem_patSet_iff h v).1 hv
        refine (mem_patSet_iff h _).2 ?_
        have e : ((u * v : GL ι K) : Matrix ι ι K) - 1 =
            ((u : Matrix ι ι K) - 1) + ((v : Matrix ι ι K) - 1) +
              ((u : Matrix ι ι K) - 1) * ((v : Matrix ι ι K) - 1) := by
          rw [Units.val_mul]
          noncomm_ring
        rw [e]
        exact (hu'.add hv').add (hu'.mul h hv')
      one_mem' := by
        refine (mem_patSet_iff h _).2 ?_
        intro i j hij
        simp at hij }
  { M with
    inv_mem' := by
      intro u hu
      have hn : orderOf u ≠ 0 := (orderOf_pos u).ne'
      have : u⁻¹ = u ^ (orderOf u - 1) :=
        inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, pow_orderOf_eq_one])
      rw [this]
      exact M.pow_mem hu _ }

theorem coe_patSubgroup (h : IsPat Φ) :
    ((patSubgroup h : Subgroup (GL ι K)) : Set (GL ι K)) = patSet K Φ := rfl

open Classical in

def fill (Φ : ι → ι → Prop) (f : {p : ι × ι // Φ p.1 p.2} → K) : Matrix ι ι K :=
  fun i j => if h : Φ i j then f ⟨(i, j), h⟩ else 0

theorem supp_fill (f : {p : ι × ι // Φ p.1 p.2} → K) : Supp Φ (fill Φ f) := by
  intro i j hij
  by_contra hΦ
  apply hij
  simp [fill, hΦ]

theorem card_patSet (h : IsPat Φ) :
    (patSet K Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} := by
  classical
  have hunit : ∀ f : {p : ι × ι // Φ p.1 p.2} → K, IsUnit (1 + fill Φ f).det := fun f => by
    rw [det_one_add h (supp_fill f)]
    exact isUnit_one
  let e : patSet K Φ ≃ ({p : ι × ι // Φ p.1 p.2} → K) :=
    { toFun := fun u p => (u.1 : Matrix ι ι K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (1 + fill Φ f) (hunit f), by
        refine (mem_patSet_iff h _).2 ?_
        show Supp Φ ((1 + fill Φ f) - 1)
        rw [add_sub_cancel_left]
        exact supp_fill f⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        show 1 + fill Φ (fun p => (u.1 : Matrix ι ι K) p.1.1 p.1.2) = (u.1 : Matrix ι ι K)
        ext i j
        have hu := (show ∀ i j, (i = j → (u.1 : Matrix ι ι K) i j = 1) ∧
          (i ≠ j → ¬Φ i j → (u.1 : Matrix ι ι K) i j = 0) from u.2) i j
        rw [Matrix.add_apply]
        simp only [fill]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, dif_neg (h.1 i), add_zero, hu.1 rfl]
        · rw [Matrix.one_apply_ne hij, zero_add]
          by_cases hΦ : Φ i j
          · rw [dif_pos hΦ]
          · rw [dif_neg hΦ, hu.2 hij hΦ]
      right_inv := fun f => by
        funext p
        show (1 + fill Φ f) p.1.1 p.1.2 = f p
        have hne : p.1.1 ≠ p.1.2 := fun e => h.1 p.1.2 (by have hp := p.2; rw [e] at hp; exact hp)
        rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
        simp only [fill]
        rw [dif_pos p.2] }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]

end GlobalTheory.CompanionTheory.PatGrp
