import Formalism.TranslateCocycles.StatementNet
import Formalism.TranslateCocycles.TranslateCocycleProofs.TranslateScale

noncomputable section
namespace Formalism.CG
open Finset

theorem net_even_pred (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

theorem net_even_succ (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

theorem netExponent : NetExponent := by
  refine ⟨fun k c => ⟨by ring, by ring, by ring⟩, fun k c p => by ring,
    fun k m => ⟨by ring, by ring, by ring⟩, fun k c hc => ?_, fun k => ?_⟩
  · obtain ⟨c, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    have h1 := net_even_pred (c + 1)
    have h2 := net_even_pred k
    have h3 := net_even_succ (k + (c + 1))
    rcases k with _ | k
    · simp only [Nat.add_sub_cancel, zero_add, Nat.zero_mul, Nat.zero_div, add_zero, mul_zero] at *
      nlinarith
    · simp only [Nat.add_sub_cancel] at *
      nlinarith
  · have h2 := net_even_pred k
    have h3 := net_even_succ k
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel] at *
      nlinarith

theorem netUnitMean : NetUnitMean := by
  intro Λ _ y X lg hy hs
  rcases isEmpty_or_nonempty Λ with h | ⟨⟨w0⟩⟩
  · simp at hs ⊢
  · have hc : (Fintype.card Λ : ℝ) ≠ 0 := by
      have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨w0⟩
      positivity
    have h1 : ∀ w, y w = y w0 := fun w => hy w w0
    have h2 : lg = (Fintype.card Λ : ℝ) * y w0 := by
      rw [← hs, Finset.sum_congr rfl (fun w _ => h1 w)]; simp
    rw [Finset.sum_congr rfl (fun w _ => by rw [h1 w]), ← Finset.mul_sum, h2]
    field_simp

theorem netReturnOfA : NetReturnOfA := by
  intro ι _ P TT hT n a R1 R2 m k hm hk hmk h1 h2 hR2
  set κ : ℝ := m * (1 + (m - 1) / (2 * k)) with hκ
  have hq0 : 0 ≤ (m - 1) / (2 * k) := div_nonneg (by linarith) (by linarith)
  have hq1 : (m - 1) / (2 * k) ≤ 1 := by rw [div_le_one (by linarith)]; exact hmk
  have hκ0 : 0 ≤ κ := by rw [hκ]; nlinarith
  have hκ2 : κ ≤ 2 * m := by rw [hκ]; nlinarith
  have hsplit : ∑ τ ∈ P, n τ = ∑ τ ∈ P \ TT, n τ + ∑ t ∈ TT, n t := (Finset.sum_sdiff hT).symm
  have e : (∑ τ ∈ P, n τ) * κ - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t)
      = κ * (∑ t ∈ TT, (n t - a t) + ∑ τ ∈ P \ TT, n τ) := by
    rw [hsplit, Finset.sum_sub_distrib, hκ]; ring
  have b1 : |∑ t ∈ TT, (n t - a t)| ≤ (TT.card : ℝ) * R1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h1).trans ?_
    simp
  have b2 : |∑ τ ∈ P \ TT, n τ| ≤ (P.card : ℝ) * R2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h2).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    have : ((P \ TT).card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    exact mul_le_mul_of_nonneg_right this hR2
  have b3 := (abs_add_le (∑ t ∈ TT, (n t - a t)) (∑ τ ∈ P \ TT, n τ)).trans (add_le_add b1 b2)
  rw [e, abs_mul, abs_of_nonneg hκ0]
  exact mul_le_mul hκ2 b3 (abs_nonneg _) (by linarith)

theorem net_prod_GL (q n : ℕ) :
    ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) = q ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n]
  have h1 : ∏ i ∈ range n, (q ^ n - q ^ i) = ∏ i ∈ range n, (q ^ i * (q ^ (n - i) - 1)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i ≤ n := (Finset.mem_range.mp hi).le
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']
  rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
  congr 1
  have h2 : ∏ i ∈ range n, (q ^ (n - i) - 1) = ∏ i ∈ range n, (q ^ (i + 1) - 1) := by
    rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    congr 2
    omega
  rw [h2, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => q ^ i - 1) 0 n 1]
  rfl

theorem net_prod_real (q : ℝ) (hq : 0 < q) (n : ℕ) :
    ∏ i ∈ Icc 1 n, (q ^ i - 1) = q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 1 n, (1 - (q ^ i)⁻¹) := by
  have h1 : ∏ i ∈ Icc 1 n, (q ^ i - 1) = ∏ i ∈ Icc 1 n, (q ^ i * (1 - (q ^ i)⁻¹)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have : q ^ i ≠ 0 := (pow_pos hq i).ne'
    field_simp
  rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  have : ∑ i ∈ Icc 1 n, i = ∑ i ∈ range (n + 1), i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp
    rfl
  rw [this, Finset.sum_range_id, Nat.add_sub_cancel, mul_comm]

theorem net_cast_prod (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    ((∏ i ∈ Icc 1 n, (q ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Icc 1 n, ((q : ℝ) ^ i - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  simp

theorem netCardGL : NetCardGL := by
  intro F _ _ n
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h1 : Nat.card (GL (Fin n) F)
      = Fintype.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (Fintype.card F ^ i - 1) := by
    rw [Matrix.card_GL_field, net_prod_GL]
  refine ⟨h1, ?_⟩
  rw [h1, Nat.cast_mul, net_cast_prod _ hq, net_prod_real _ (by exact_mod_cast hq), Nat.cast_pow,
    ← mul_assoc, ← pow_add, netExponent.2.2.2.2 n]

section Pattern
variable {F : Type} [Field F] {n : ℕ} {S : Finset (Fin n × Fin n)}

theorem net_pattern_one : netHasPattern S (1 : Matrix (Fin n) (Fin n) F) := by
  intro i j _
  exact Matrix.one_apply

theorem net_pattern_det (hS : ∀ x ∈ S, x.1 < x.2) {A : Matrix (Fin n) (Fin n) F}
    (hA : netHasPattern S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hn : (i, j) ∉ S := fun h => absurd (hS _ h) (not_lt.mpr (le_of_lt hij'))
    rw [hA i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun h => lt_irrefl _ (hS _ h)
  rw [hA i i hn, if_pos rfl]

theorem net_pattern_mul (hS : ∀ x ∈ S, x.1 < x.2)
    (hT : ∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S) {A B : Matrix (Fin n) (Fin n) F}
    (hA : netHasPattern S A) (hB : netHasPattern S B) : netHasPattern S (A * B) := by
  intro i l hil
  rw [Matrix.mul_apply]
  have hterm : ∀ j, A i j * B j l = if j = i then (if i = l then 1 else 0) else 0 := by
    intro j
    by_cases hji : j = i
    · subst hji
      have hn : (j, j) ∉ S := fun h => lt_irrefl _ (hS _ h)
      rw [hA j j hn, hB j l hil]; simp
    · rw [if_neg hji]
      by_cases h1 : (i, j) ∈ S
      · by_cases hjl : j = l
        · subst hjl; exact absurd h1 hil
        · have h2 : (j, l) ∉ S := fun h => hil (hT i j l h1 h)
          rw [hB j l h2, if_neg hjl, mul_zero]
      · rw [hA i j h1, if_neg (fun h => hji h.symm), zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp

end Pattern

theorem netPatternGroup : NetPatternGroup := by
  intro F _ _ n S hS hT
  classical
  let M : Submonoid (GL (Fin n) F) :=
    { carrier := {A | netHasPattern S (A : Matrix (Fin n) (Fin n) F)}
      mul_mem' := fun {A B} hA hB => by
        simpa using net_pattern_mul hS hT hA hB
      one_mem' := by simpa using (net_pattern_one (F := F) (S := S)) }
  let H : Subgroup (GL (Fin n) F) :=
    { M with
      inv_mem' := fun {A} hA => by
        obtain ⟨N, hN, hAN⟩ := (isOfFinOrder_iff_pow_eq_one).mp (isOfFinOrder_of_finite A)
        have : A⁻¹ = A ^ (N - 1) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ', Nat.sub_add_cancel hN, hAN]
        rw [this]
        exact M.pow_mem hA _ }
  refine ⟨H, fun A => Iff.rfl, ?_⟩
  let φ : H → (S → F) := fun A s => (A.1 : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  have hφ : Function.Bijective φ := by
    constructor
    · intro A B hAB
      apply Subtype.ext
      apply Units.ext
      ext i j
      by_cases h : (i, j) ∈ S
      · exact congrFun hAB ⟨(i, j), h⟩
      · rw [A.2 i j h, B.2 i j h]
    · intro f
      let A0 : Matrix (Fin n) (Fin n) F :=
        fun i j => if h : (i, j) ∈ S then f ⟨(i, j), h⟩ else if i = j then 1 else 0
      have hA0 : netHasPattern S A0 := fun i j h => by simp only [A0, dif_neg h]
      have hdet : A0.det ≠ 0 := by rw [net_pattern_det hS hA0]; exact one_ne_zero
      refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A0 hdet, hA0⟩, ?_⟩
      funext s
      show A0 s.1.1 s.1.2 = f s
      simp only [A0, Prod.mk.eta, dif_pos s.2]
  rw [Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_coe]

theorem net_full_card (n : ℕ) : (netFull n).card = n * (n - 1) / 2 := by
  unfold netFull
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if (i, j).1 < (i, j).2 then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => (i, j).1 < (i, j).2) = Finset.Iio j := by
      ext i; simp
    rw [this, Fin.card_Iio]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) n,
    Finset.sum_range_id]

theorem net_removed_card (k c p0 : ℕ) (hp : p0 < c) :
    ((netFull (k + c)).filter fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k).card = k := by
  have : ((netFull (k + c)).filter fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k)
      = (univ : Finset (Fin k)).image
          (fun i : Fin k => ((⟨p0 + i.val, by have := i.2; omega⟩ : Fin (k + c)),
            (⟨p0 + k, by omega⟩ : Fin (k + c)))) := by
    ext ⟨a, b⟩
    simp only [netFull, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq, Fin.lt_def, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨a.val - p0, by omega⟩, by simp only []; omega, h3.symm⟩
    · rintro ⟨i, h1, h2⟩
      have := i.2
      omega
  rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j hij
  simp only [Prod.mk.injEq, Fin.ext_iff, and_true] at hij
  exact Fin.ext (by omega)

theorem netPatternCard : NetPatternCard := by
  refine ⟨fun n => ⟨net_full_card n, ?_⟩, fun k c p0 hp => ⟨?_, ?_⟩⟩
  · intro i j l h1 h2
    simp only [netFull, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact lt_trans h1 h2
  · have h1 := Finset.card_filter_add_card_filter_not (s := netFull (k + c))
      (fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k)
    have h2 : ((netFull (k + c)).filter fun x => ¬ (p0 ≤ x.1.val ∧ x.2.val = p0 + k))
        = netPattern k c p0 := by
      unfold netFull netPattern
      rw [Finset.filter_filter]
    rw [h2, net_removed_card k c p0 hp, net_full_card] at h1
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    have e1 := net_even_pred (d + 1)
    have e2 := net_even_pred k
    have e3 := net_even_pred (k + (d + 1))
    rcases k with _ | k
    · simp only [Nat.add_sub_cancel, zero_add, Nat.zero_mul, Nat.zero_div, add_zero, mul_zero] at *
      omega
    · have e4 : k + 1 + (d + 1) - 1 = k + 1 + d := by omega
      simp only [Nat.add_sub_cancel, e4] at *
      nlinarith
  · intro i j l h1 h2
    simp only [netPattern, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at *
    omega

theorem net_index_real (F : Type) [Field F] [Fintype F] (n e E : ℕ) (H : Subgroup (GL (Fin n) F))
    (hH : Nat.card H = Fintype.card F ^ e) (hE : e + E = n ^ 2) :
    (H.index : ℝ) = (Fintype.card F : ℝ) ^ E * ∏ i ∈ Icc 1 n, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 : (H.index : ℝ) * (Fintype.card F : ℝ) ^ e = (Nat.card (GL (Fin n) F) : ℝ) := by
    rw [← H.index_mul_card, hH]; push_cast; ring
  rw [(netCardGL F n).2, ← hE, pow_add] at h1
  have h2 : (Fintype.card F : ℝ) ^ e ≠ 0 := (pow_pos hq e).ne'
  apply mul_right_cancel₀ h2
  rw [h1]; ring

theorem net_card_of_pattern (F : Type) [Field F] [Fintype F] (n : ℕ) (S : Finset (Fin n × Fin n))
    (hS : ∀ x ∈ S, x.1 < x.2) (hT : ∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S)
    (H : Subgroup (GL (Fin n) F))
    (hH : ∀ A : GL (Fin n) F, A ∈ H ↔ netHasPattern S (A : Matrix (Fin n) (Fin n) F)) :
    Nat.card H = Fintype.card F ^ S.card := by
  obtain ⟨H', h1, h2⟩ := netPatternGroup F n S hS hT
  have : H = H' := Subgroup.ext fun A => by rw [hH, h1]
  rw [this, h2]

theorem net_factor_pos (q : ℝ) (hq : 1 < q) (i : ℕ) (hi : 1 ≤ i) : 0 < 1 - (q ^ i)⁻¹ := by
  have : 1 < q ^ i := one_lt_pow₀ hq (by omega)
  have := inv_lt_one_of_one_lt₀ this
  linarith

theorem netBalanceG : NetBalanceG := by
  intro J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA rL rLb Etw
    h1 hA h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2
  have hb := balanceG J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA
    rL rLb Etw h1 hA h4 h5
  have hr := netReturnOfA ℕ P T hTP n top R1 R2 (J.card : ℝ) k (by exact_mod_cast hJ) hk hJk hn1 hn2
    hR2
  have hr' := (abs_le.mp hr).1
  have e : ∑ j ∈ J, ∑ τ ∈ P, (w j τ + e1 j τ + e2 j τ)
      = ∑ j ∈ J, ∑ τ ∈ P, w j τ + ∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun τ _ => ?_; ring
  rw [e] at hb
  linarith

theorem net_sum_inv {Λ : Type} [Fintype Λ] (c : Λ → Λ) (hc : Function.Involutive c) (X : Λ → ℝ) :
    ∑ u, X (c u) = ∑ u, X u := by
  have := Equiv.sum_comp (hc.toPerm c) X
  simpa only [Function.Involutive.coe_toPerm] using this

theorem netBalanceMean : NetBalanceMean := by
  intro Λ _ _ c hc y lg hy hys hlg J T P D del hD hdel col r a eta Dpi Dp Dm top k w e1 e2 Ecol CA Etw
    h1 hA h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2
  set N : ℝ := (Fintype.card Λ : ℝ) with hN
  have hN0 : 0 < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  set m : ℝ := (J.card : ℝ) with hm
  set R' : ℝ := (∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k))) with hR'
  set K : ℝ := -(∑ j ∈ J, ∑ τ ∈ P, w j τ) + m * (m - 1) / (2 * k) * ∑ t ∈ T, top t
      - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + Ecol + m * CA + Etw / (2 * D)
          + 2 * m * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2)) with hK
  let X : Λ → ℝ := fun u => 2 * col u - ∑ j ∈ J, a j u / D
  have hu : ∀ u, K - ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) - m * ((r u + r (c u)) / (del * D))
      ≤ (X u + X (c u)) / 2 + R' := by
    intro u
    have := netBalanceG J T P D del hD hdel (col u) (col (c u)) (fun j => a j u) (fun j => a j (c u))
      Dpi Dp Dm (fun j => eta j u) (fun j => eta j (c u)) top k w e1 e2 Ecol CA (r u) (r (c u)) Etw
      (h1 u) (hA u) h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2
    have e : ∑ j ∈ J, (a j u + a j (c u)) / D = ∑ j ∈ J, a j u / D + ∑ j ∈ J, a j (c u) / D := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    simp only [X]
    rw [e] at this
    rw [hK, hR']
    linarith
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ (univ : Finset Λ)) => hu u)
  have eR : ∑ u, ((X u + X (c u)) / 2 + R') = ∑ u, X u + N * R' := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, net_sum_inv c hc X]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have eE : ∑ u, ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) = ∑ j ∈ J, (∑ u, eta j u) / D := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_div, Finset.sum_add_distrib, net_sum_inv c hc (eta j)]
    field_simp
    ring
  have eL : ∑ u, (K - ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D)
        - m * ((r u + r (c u)) / (del * D)))
      = N * K - ∑ j ∈ J, (∑ u, eta j u) / D - m * ((∑ u, (r u + r (c u))) / (del * D)) := by
    have e3 : ∑ u, m * ((r u + r (c u)) / (del * D)) = m * ((∑ u, (r u + r (c u))) / (del * D)) := by
      rw [← Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, eE, e3]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  rw [eL, eR] at hs
  have hy' := netUnitMean Λ y X lg hy hys
  have eM : ∑ j ∈ J, ((∑ u, eta j u) / N) / D = (∑ j ∈ J, (∑ u, eta j u) / D) / N := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  have hfin := mul_le_mul_of_nonneg_left hs (div_nonneg hlg hN0.le)
  show _ ≤ ∑ u, y u * X u + _
  rw [hy', eM]
  have g1 : lg / N * (N * K - ∑ j ∈ J, (∑ u, eta j u) / D
        - m * ((∑ u, (r u + r (c u))) / (del * D)))
      = lg * (-(∑ j ∈ J, ∑ τ ∈ P, w j τ) + m * (m - 1) / (2 * k) * ∑ t ∈ T, top t
        - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + (∑ j ∈ J, (∑ u, eta j u) / D) / N + Ecol
            + m * (CA + ((∑ u, (r u + r (c u))) / N) / (del * D)) + Etw / (2 * D)
            + 2 * m * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2))) := by
    rw [hK]
    field_simp
    ring
  have g2 : lg / N * (∑ u, X u + N * R') = lg * ((∑ u, X u) / N) + R' * lg := by
    field_simp
  rw [g1, g2] at hfin
  exact hfin

end Formalism.CG
