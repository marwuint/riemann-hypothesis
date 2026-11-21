import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.LemmaH

theorem two_sum_Ico (a d : ℕ) :
    2 * ∑ i ∈ Finset.Ico a (a + d), (i : ℝ) = d * (2 * a + d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem sum_le_top (A : Finset ℕ) : ∀ t : ℕ, (∀ a ∈ A, a < t) →
    2 * ∑ i ∈ A, (i : ℝ) + (A.card : ℝ) * ((A.card : ℝ) + 1) ≤ 2 * (A.card : ℝ) * t := by
  induction A using Finset.induction_on_max with
  | empty => intro t _; simp
  | insert a A hA ih =>
    intro t ht
    have hnot : a ∉ A := fun h => lt_irrefl _ (hA a h)
    have h1 := ih a hA
    have h2 : (a : ℝ) + 1 ≤ t := by exact_mod_cast ht a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hnot, Finset.card_insert_of_notMem hnot]
    push_cast
    have hc : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    nlinarith [mul_nonneg (add_nonneg hc zero_le_one) (sub_nonneg.2 h2)]

theorem abel (z d : ℕ → ℝ) (N : ℕ) (hz : ∀ i, i < N → 1 ≤ z i - z (i + 1))
    (hD : ∀ j, j ≤ N + 1 → 0 ≤ ∑ i ∈ Finset.range j, d i) :
    ∀ m, m ≤ N → z m * ∑ i ∈ Finset.range (m + 1), d i +
      ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1), d i ≤ ∑ i ∈ Finset.range (m + 1), z i * d i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hzz := hz m (by omega)
    have hD0 := hD (m + 1) (by omega)
    have e1 : ∑ i ∈ Finset.range (m + 1 + 1), d i = ∑ i ∈ Finset.range (m + 1), d i + d (m + 1) :=
      Finset.sum_range_succ _ _
    have e2 : ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1), d i =
        ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range (j + 1), d i + ∑ i ∈ Finset.range (m + 1), d i :=
      Finset.sum_range_succ _ _
    have e3 : ∑ i ∈ Finset.range (m + 1 + 1), z i * d i =
        ∑ i ∈ Finset.range (m + 1), z i * d i + z (m + 1) * d (m + 1) :=
      Finset.sum_range_succ _ _
    rw [e1, e2, e3]
    nlinarith [mul_nonneg (sub_nonneg.2 hzz) hD0]

theorem eq_of_dom (N : ℕ) (m y : ℕ → ℝ)
    (hs : ∀ i, i < N → 1 ≤ (m i + y i) - (m (i + 1) + y (i + 1)))
    (hdom : ∀ j, j ≤ N + 1 → ∑ i ∈ Finset.range j, y i ≤ ∑ i ∈ Finset.range j, m i)
    (htot : ∑ i ∈ Finset.range (N + 1), y i = ∑ i ∈ Finset.range (N + 1), m i)
    (hsq : ∑ i ∈ Finset.range (N + 1), (m i) ^ 2 ≤ ∑ i ∈ Finset.range (N + 1), (y i) ^ 2) :
    ∀ i, i < N + 1 → y i = m i := by
  set d : ℕ → ℝ := fun i => m i - y i with hd
  have hDsum : ∀ j, ∑ i ∈ Finset.range j, d i = ∑ i ∈ Finset.range j, m i - ∑ i ∈ Finset.range j, y i := by
    intro j
    simp only [hd, Finset.sum_sub_distrib]
  have hD : ∀ j, j ≤ N + 1 → 0 ≤ ∑ i ∈ Finset.range j, d i := by
    intro j hj
    rw [hDsum]
    linarith [hdom j hj]
  have hDN : ∑ i ∈ Finset.range (N + 1), d i = 0 := by
    rw [hDsum, htot]; ring
  have hab := abel (fun i => m i + y i) d N hs hD N le_rfl
  rw [hDN, mul_zero, zero_add] at hab
  have hzd : ∑ i ∈ Finset.range (N + 1), (m i + y i) * d i ≤ 0 := by
    have : ∑ i ∈ Finset.range (N + 1), (m i + y i) * d i =
        ∑ i ∈ Finset.range (N + 1), (m i) ^ 2 - ∑ i ∈ Finset.range (N + 1), (y i) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [hd]; ring
    rw [this]
    linarith
  have hz0 : ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), d i = 0 :=
    le_antisymm (le_trans hab hzd) (Finset.sum_nonneg fun j hj => hD _ (by
      have := Finset.mem_range.1 hj
      omega))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hD _ (by
      have := Finset.mem_range.1 hj
      omega))).1 hz0
  have hzero : ∀ j, j ≤ N + 1 → ∑ i ∈ Finset.range j, d i = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    rcases Nat.lt_or_ge j (N + 1) with h | h
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact hall j' (Finset.mem_range.2 (by omega))
    · have : j = N + 1 := by omega
      rw [this]; exact hDN
  intro i hi
  have h1 := hzero i (by omega)
  have h2 := hzero (i + 1) (by omega)
  rw [Finset.sum_range_succ, h1, zero_add] at h2
  simp only [hd] at h2
  linarith

variable {n : ℕ}

def ex (f : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then f ⟨i, h⟩ else 0

theorem ex_mk (f : Fin n → ℝ) {i : ℕ} (h : i < n) : ex f i = f ⟨i, h⟩ := dif_pos h

theorem ex_val (f : Fin n → ℝ) (a : Fin n) : ex f (a : ℕ) = f a := by
  rw [ex_mk f a.2]

theorem map_filter_lt {k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun a : Fin n => (a : ℕ) < k)).map Fin.valEmbedding = Finset.range k := by
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hi
    exact ⟨⟨i, by omega⟩, hi, rfl⟩

theorem card_filter_lt {k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun a : Fin n => (a : ℕ) < k)).card = k := by
  have := congrArg Finset.card (map_filter_lt hk)
  simpa using this

theorem sum_range_of (f : Fin n → ℝ) (G : ℕ → ℝ) {k : ℕ} (hk : k ≤ n)
    (hG : ∀ a : Fin n, G a = f a) :
    ∑ i ∈ Finset.range k, G i = ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), f a := by
  rw [← map_filter_lt hk, Finset.sum_map]
  exact Finset.sum_congr rfl fun a _ => hG a

end GlobalTheory.CompanionTheory.RealCount.LemmaH

namespace GlobalTheory.CompanionTheory.RealCount

end GlobalTheory.CompanionTheory.RealCount
