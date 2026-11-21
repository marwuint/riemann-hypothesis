import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.DomGLVal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def Integ (g : GL (Fin n) L) : Prop :=
  (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
    ∀ i j, j < i → Valued.v ((g : Matrix (Fin n) (Fin n) L) i j) < 1

theorem mulVec_mem_latK {g : GL (Fin n) L} (hg : Integ g) {k : ℕ} {x : Fin n → L} (hx : x ∈ latK L n k) :
    (g : Matrix (Fin n) (Fin n) L).mulVec x ∈ latK L n k := by
  have hx1 : ∀ j, Valued.v (x j) ≤ 1 := fun j => by
    have := hx j
    split_ifs at this
    · exact this
    · exact this.le
  intro i
  have e : ((g : Matrix (Fin n) (Fin n) L).mulVec x) i = ∑ j, (g : Matrix (Fin n) (Fin n) L) i j * x j := rfl
  rw [e]
  split_ifs with hi
  · refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hg.1 i j) (hx1 j)
  · refine Valuation.map_sum_lt (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) one_ne_zero fun j _ => ?_
    rw [map_mul]
    by_cases hj : j.val < k
    · have hji : j < i := by
        rw [Fin.lt_def]; omega
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hx1 j)) (hg.2 i j hji)
    · have := hx j
      rw [if_neg hj] at this
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hg.1 i j)) this

theorem integ_of_stable {g : GL (Fin n) L}
    (h : ∀ k : ℕ, k ≤ n → ∀ x ∈ latK L n k, (g : Matrix (Fin n) (Fin n) L).mulVec x ∈ latK L n k) : Integ g := by
  have hs : ∀ (k : ℕ) (j : Fin n), j.val < k → (Pi.single j 1 : Fin n → L) ∈ latK L n k := by
    intro k j hj a
    by_cases haj : a = j
    · subst haj
      simp [hj]
    · simp only [Pi.single_eq_of_ne haj, map_zero]
      split_ifs <;> simp
  constructor
  · intro i j
    have := h n le_rfl _ (hs n j j.2) i
    rw [if_pos i.2] at this
    simpa using this
  · intro i j hji
    have := h i.val i.2.le _ (hs i.val j hji) i
    rw [if_neg (lt_irrefl _)] at this
    simpa using this

theorem mem_IwGL_iff (g : GL (Fin n) L) : g ∈ IwGL L n ↔ Integ g ∧ Integ g⁻¹ := by
  have key : ∀ (h : GL (Fin n) L) (y : Fin n → L),
      (Matrix.GeneralLinearGroup.toLin h) • y = (h : Matrix (Fin n) (Fin n) L).mulVec y := by
    intro h y
    rfl
  have key2 : ∀ (h : GL (Fin n) L) (S : Set (Fin n → L)), (Matrix.GeneralLinearGroup.toLin h) • S = S ↔
      ((∀ x ∈ S, (h : Matrix (Fin n) (Fin n) L).mulVec x ∈ S) ∧
        ∀ x ∈ S, ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x ∈ S) := by
    intro h S
    have inv1 : ∀ y : Fin n → L, (h : Matrix (Fin n) (Fin n) L).mulVec
        (((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have inv2 : ∀ y : Fin n → L, ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec
        ((h : Matrix (Fin n) (Fin n) L).mulVec y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    constructor
    · intro hS
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [← hS]
        exact Set.mem_smul_set.2 ⟨x, hx, key h x⟩
      · rw [← hS] at hx
        obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
        rw [key, inv2]
        exact hy
    · rintro ⟨h1, h2⟩
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.1 hy
        rw [key]
        exact h1 x hx
      · intro hy
        exact Set.mem_smul_set.2 ⟨_, h2 y hy, by rw [key, inv1]⟩
  simp only [IwGL, Subgroup.mem_iInf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h' : ∀ k : Fin (n + 1), _ := fun k => (key2 g _).1 (h k)
    exact ⟨integ_of_stable fun k hk => (h' ⟨k, Nat.lt_succ_of_le hk⟩).1,
      integ_of_stable fun k hk => (h' ⟨k, Nat.lt_succ_of_le hk⟩).2⟩
  · rintro ⟨h1, h2⟩ k
    exact (key2 g _).2 ⟨fun x hx => mulVec_mem_latK h1 hx, fun x hx => mulVec_mem_latK h2 hx⟩

theorem val_inv_diag {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) :
    ((s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (e i)⁻¹) := by
  have h1 : (s : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i => (e i)⁻¹) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (he i)
  calc ((s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      = ((s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((s : Matrix (Fin n) (Fin n) L) *
          Matrix.diagonal (fun i => (e i)⁻¹)) := by rw [h1, mul_one]
    _ = _ := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem conj_apply {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) (g : GL (Fin n) L) (i j : Fin n) :
    ((s * g * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      e i * (g : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, val_inv_diag he hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diag_data {t : GL (Fin n) L} (ht : IsDiagM t) :
    (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (t : Matrix (Fin n) (Fin n) L) i i) ∧
      ∀ i, (t : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have h1 : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (t : Matrix (Fin n) (Fin n) L) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact ht i j hij
  refine ⟨h1, fun i hi => ?_⟩
  have hd : (t : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 t.isUnit
    exact this.ne_zero
  rw [h1, Matrix.det_diagonal] at hd
  exact hd (Finset.prod_eq_zero (Finset.mem_univ i) hi)

def cc : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

theorem cc_lt_one : cc < 1 := by
  rw [cc, ← WithZero.coe_one, WithZero.coe_lt_coe]
  exact Multiplicative.ofAdd_lt.2 (by norm_num)

theorem ordL_eq {a : L} {A : Multiplicative ℤ} (h : Valued.v a = (A : WithZero (Multiplicative ℤ))) :
    ordL a = -Multiplicative.toAdd A := by
  have h0 : Valued.v a ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [ordL, dif_neg h0]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_unzero, h]

theorem v_le_of_ordL_le {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordL a ≤ ordL b) :
    Valued.v b ≤ Valued.v a := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  obtain ⟨A, hA⟩ := WithZero.ne_zero_iff_exists.1 ha'
  obtain ⟨B, hB⟩ := WithZero.ne_zero_iff_exists.1 hb'
  rw [ordL_eq hA.symm, ordL_eq hB.symm] at h
  rw [← hA, ← hB, WithZero.coe_le_coe]
  exact Multiplicative.toAdd_le.1 (by omega)

theorem v_le_of_ordL_lt {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordL a < ordL b) :
    Valued.v b ≤ cc * Valued.v a := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  obtain ⟨A, hA⟩ := WithZero.ne_zero_iff_exists.1 ha'
  obtain ⟨B, hB⟩ := WithZero.ne_zero_iff_exists.1 hb'
  rw [ordL_eq hA.symm, ordL_eq hB.symm] at h
  rw [← hA, ← hB, cc, ← WithZero.coe_mul, WithZero.coe_le_coe]
  refine Multiplicative.toAdd_le.1 ?_
  rw [toAdd_mul, toAdd_ofAdd]
  omega

theorem exists_pow_mul_le (y : WithZero (Multiplicative ℤ)) : ∃ m₀ : ℕ, ∀ m ≥ m₀, cc ^ m * y ≤ 1 := by
  by_cases hy : y = 0
  · exact ⟨0, fun m _ => by simp [hy]⟩
  obtain ⟨m₀, hm⟩ := exists_pow_lt₀ cc_lt_one (Units.mk0 y⁻¹ (inv_ne_zero hy))
  refine ⟨m₀, fun m hm' => ?_⟩
  have h1 : cc ^ m ≤ cc ^ m₀ := pow_le_pow_right_of_le_one' cc_lt_one.le hm'
  have h2 : cc ^ m ≤ y⁻¹ := h1.trans (le_of_lt (by simpa using hm))
  calc cc ^ m * y ≤ y⁻¹ * y := by gcongr
    _ = 1 := inv_mul_cancel₀ hy

theorem conj_inv (s g : GL (Fin n) L) : (s * g * s⁻¹)⁻¹ = s * g⁻¹ * s⁻¹ := by group

theorem integ_up {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) {g : GL (Fin n) L} (hg : IsUniM g)
    (h : ∀ i j, i < j → Valued.v (e i * (g : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹) ≤ 1) :
    Integ (s * g * s⁻¹) ∧ IsUniM (s * g * s⁻¹) := by
  have hlow : ∀ i j, j < i → ((s * g * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 :=
    fun i j hji => by rw [conj_apply he hs, hg.1 i j hji]; simp
  have hdiag : ∀ i, ((s * g * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 :=
    fun i => by rw [conj_apply he hs, hg.2 i, mul_one, mul_inv_cancel₀ (he i)]
  refine ⟨⟨fun i j => ?_, fun i j hji => ?_⟩, hlow, hdiag⟩
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [conj_apply he hs]; exact h i j hij
    · rw [hdiag]; simp
    · rw [hlow i j hij]; simp
  · rw [hlow i j hji]; simp

theorem integ_low {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) {g : GL (Fin n) L} (hg : IsLowUniM g)
    (h : ∀ i j, j < i → Valued.v (e i * (g : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹) < 1) :
    Integ (s * g * s⁻¹) ∧ IsLowUniM (s * g * s⁻¹) := by
  have hup : ∀ i j, i < j → ((s * g * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 :=
    fun i j hij => by rw [conj_apply he hs, hg.1 i j hij]; simp
  have hdiag : ∀ i, ((s * g * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 :=
    fun i => by rw [conj_apply he hs, hg.2 i, mul_one, mul_inv_cancel₀ (he i)]
  refine ⟨⟨fun i j => ?_, fun i j hji => ?_⟩, hup, hdiag⟩
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [hup i j hij]; simp
    · rw [hdiag]; simp
    · rw [conj_apply he hs]; exact (h i j hij).le
  · rw [conj_apply he hs]; exact h i j hji

theorem up_mem {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) {g : GL (Fin n) L} (hg : IsUniM g)
    (hg' : IsUniM g⁻¹)
    (h : ∀ i j, i < j → Valued.v (e i * (g : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹) ≤ 1)
    (h' : ∀ i j, i < j → Valued.v (e i * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹) ≤ 1) :
    s * g * s⁻¹ ∈ IwGL L n ∧ IsUniM (s * g * s⁻¹) :=
  ⟨(mem_IwGL_iff _).2 ⟨(integ_up he hs hg h).1, by rw [conj_inv]; exact (integ_up he hs hg' h').1⟩,
    (integ_up he hs hg h).2⟩

theorem low_mem {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) {g : GL (Fin n) L} (hg : IsLowUniM g)
    (hg' : IsLowUniM g⁻¹)
    (h : ∀ i j, j < i → Valued.v (e i * (g : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹) < 1)
    (h' : ∀ i j, j < i → Valued.v (e i * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹) < 1) :
    s * g * s⁻¹ ∈ IwGL L n ∧ IsLowUniM (s * g * s⁻¹) :=
  ⟨(mem_IwGL_iff _).2 ⟨(integ_low he hs hg h).1, by rw [conj_inv]; exact (integ_low he hs hg' h').1⟩,
    (integ_low he hs hg h).2⟩

theorem low_close {s : GL (Fin n) L} {e : Fin n → L} (he : ∀ i, e i ≠ 0)
    (hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e) {g : GL (Fin n) L} (hg : IsLowUniM g)
    {B : WithZero (Multiplicative ℤ)}
    (h : ∀ a b, b < a → Valued.v (e a * (g : Matrix (Fin n) (Fin n) L) a b * (e b)⁻¹) ≤ B) (a b : Fin n) :
    Valued.v (((s * g * s⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b -
      (1 : Matrix (Fin n) (Fin n) L) a b) ≤ B := by
  rw [conj_apply he hs]
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [hg.1 a b hab, Matrix.one_apply_ne hab.ne]
    simp
  · rw [hg.2 a, mul_one, mul_inv_cancel₀ (he a), Matrix.one_apply_eq]
    simp
  · rw [Matrix.one_apply_ne hab.ne', sub_zero]
    exact h a b hab

theorem valuation_triple_mul_le {x y z : L} {B : WithZero (Multiplicative ℤ)} (h1 : Valued.v x * Valued.v z ≤ B)
    (h2 : Valued.v y ≤ 1) : Valued.v (x * y * z) ≤ B := by
  rw [map_mul, map_mul, mul_right_comm]
  exact (mul_le_of_le_one_right' h2).trans h1

theorem valuation_triple_mul_lt_one {x y z : L} (h1 : Valued.v x * Valued.v z ≤ 1) (h2 : Valued.v y < 1) :
    Valued.v (x * y * z) < 1 := by
  rw [map_mul, map_mul, mul_right_comm]
  exact (mul_le_of_le_one_left' h1).trans_lt h2

theorem ratio_le {a b : L} (ha : a ≠ 0) (h : Valued.v b ≤ Valued.v a) :
    Valued.v b * Valued.v a⁻¹ ≤ 1 := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [map_inv₀]
  calc Valued.v b * (Valued.v a)⁻¹ ≤ Valued.v a * (Valued.v a)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ ha'

theorem ratio_pow_le {a b : L} (ha : a ≠ 0) (h : Valued.v b ≤ cc * Valued.v a) (m : ℕ) :
    Valued.v (b ^ m) * Valued.v (a ^ m)⁻¹ ≤ cc ^ m := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [map_inv₀, map_pow, map_pow]
  have h1 : Valued.v b ^ m ≤ (cc * Valued.v a) ^ m := by gcongr
  calc Valued.v b ^ m * (Valued.v a ^ m)⁻¹ ≤ (cc * Valued.v a) ^ m * (Valued.v a ^ m)⁻¹ := by gcongr
    _ = cc ^ m := by rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha'), mul_one]

section Top

open Filter Topology

theorem ev_ball (x : L) (A : Set L) (hA : A ∈ 𝓝 x) :
    ∀ᶠ m : ℕ in atTop, {y : L | Valued.v (y - x) ≤ cc ^ m} ⊆ A := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hA
  obtain ⟨m₀, hm⟩ := exists_pow_lt₀ cc_lt_one
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := .ofClass (Valued.v : Valuation L (WithZero (Multiplicative ℤ))))) γ)
  filter_upwards [eventually_ge_atTop m₀] with m hm' y hy
  refine hγ ?_
  have h2 : Valued.v (y - x) < _ := lt_of_le_of_lt (le_trans hy (pow_le_pow_right_of_le_one' cc_lt_one.le hm')) hm
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 h2

theorem ev_pi {ι X : Type} [Finite ι] [TopologicalSpace X] (a : ι → X) (S : ℕ → X → Set X)
    (h : ∀ x, ∀ A ∈ 𝓝 x, ∀ᶠ m in atTop, S m x ⊆ A) (A : Set (ι → X)) (hA : A ∈ 𝓝 a) :
    ∀ᶠ m in atTop, {b : ι → X | ∀ i, b i ∈ S m (a i)} ⊆ A := by
  rw [nhds_pi, Filter.mem_pi] at hA
  obtain ⟨I, hI, t, ht, hsub⟩ := hA
  have : ∀ᶠ m in atTop, ∀ i, S m (a i) ⊆ t i :=
    eventually_all.2 fun i => h _ _ (ht i)
  filter_upwards [this] with m hm b hb
  exact hsub fun i _ => hm i (hb i)

theorem ev_mat (A : Set (Matrix (Fin n) (Fin n) L)) (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L)) :
    ∀ᶠ m : ℕ in atTop, ∀ M : Matrix (Fin n) (Fin n) L,
      (∀ a b, Valued.v (M a b - (1 : Matrix (Fin n) (Fin n) L) a b) ≤ cc ^ m) → M ∈ A := by
  have := ev_pi (ι := Fin n) (X := Fin n → L) (1 : Matrix (Fin n) (Fin n) L)
    (fun m r => {b : Fin n → L | ∀ j, b j ∈ {y : L | Valued.v (y - r j) ≤ cc ^ m}})
    (fun r => ev_pi r (fun m x => {y : L | Valued.v (y - x) ≤ cc ^ m}) ev_ball) A hA
  filter_upwards [this] with m hm M hM
  exact hm fun a b => hM a b

theorem open_shrink (U : Set (GL (Fin n) L)) (hU : IsOpen U) (h1 : (1 : GL (Fin n) L) ∈ U) :
    ∃ m : ℕ, ∀ g : GL (Fin n) L,
      (∀ a b, Valued.v ((g : Matrix (Fin n) (Fin n) L) a b - (1 : Matrix (Fin n) (Fin n) L) a b) ≤ cc ^ m) →
      (∀ a b, Valued.v (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b -
        (1 : Matrix (Fin n) (Fin n) L) a b) ≤ cc ^ m) → g ∈ U := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
  have hΦ : Continuous (fun p : Matrix (Fin n) (Fin n) L × Matrix (Fin n) (Fin n) L =>
      (p.1, MulOpposite.op p.2)) := continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd)
  have hmem : ((1 : Matrix (Fin n) (Fin n) L), (1 : Matrix (Fin n) (Fin n) L)) ∈ (fun p :
      Matrix (Fin n) (Fin n) L × Matrix (Fin n) (Fin n) L => (p.1, MulOpposite.op p.2)) ⁻¹' W := by
    have h2 : Units.embedProduct (Matrix (Fin n) (Fin n) L) (1 : GL (Fin n) L) ∈ W := h1
    rw [map_one] at h2
    exact h2
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 ((hW.preimage hΦ).mem_nhds hmem)
  obtain ⟨m, hmA, hmB⟩ := ((ev_mat A hA).and (ev_mat B hB)).exists
  refine ⟨m, fun g c1 c2 => ?_⟩
  exact hAB (Set.mk_mem_prod (hmA _ c1) (hmB _ c2))

end Top

end GlobalTheory.CompanionTheory.DomGLVal
