import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.RamifiedLoss

open Formalism.MainNotions.G GlobalTheory.HCEntries GlobalTheory.FockDegreeGap

variable {D : D7} {L : SizeData₂ D}

theorem ramifiedTau1_ne_ramifiedTau2 {φ : Formalism.HC.Frame} (t t' : φ.A) : φ.tau1 t ≠ φ.tau2 t' := by
  intro h
  have h1 := congrArg (fun g : φ.GG => g.1.1) h
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  exact absurd h1 (by decide)

theorem eTau_false (D : D7) (t : HH D) :
    (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]
  rfl

theorem eTau_true (D : D7) (t : HH D) :
    (D.eTau (tauPl D (true, t)) : D.R.GG) = D.R.tau2 t := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]
  rfl

theorem false_not_thick (D : D7) (t : HH D) :
    (D.eTau (tauPl D (false, t)) : D.R.GG) ∉ D.host.thickPlaces := by
  rw [eTau_false]
  intro h
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
  exact ramifiedTau1_ne_ramifiedTau2 _ _ hs.symm

theorem true_not_top (D : D7) (t : HH D) :
    (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_true]
  intro h
  obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
  exact ramifiedTau1_ne_ramifiedTau2 _ _ hs

theorem false_not_top {t : HH D} (ht : t ∉ D.host.TT) :
    (D.eTau (tauPl D (false, t)) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_false]
  intro h
  obtain ⟨s, hs, he⟩ := Finset.mem_image.1 h
  have hst : s = t := D.R.iota_bijective.1 (congrArg Prod.snd he)
  exact ht (hst ▸ hs)

theorem k_b'_le (h : SizeLstar L) : (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b := by
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hn := one_le_n D
  have hL := one_le_scL L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by
    have : D.R.m ≤ D.R.t := by have := D.R.three_m_lt_t; omega
    exact_mod_cast this
  have h0 : 0 ≤ szlStar L := by unfold szlStar; positivity
  have h1 : (D.R.k : ℝ) * szlStar L ≤ L.sc.b := by
    unfold szlStar
    rw [← mul_div_assoc, div_le_iff₀ (by positivity), ← mul_assoc, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have e2 : L.Sc + D.R.t + L.sc.L ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hn)
    have e1 : (D.R.k : ℝ) * D.R.m ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e3 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    linarith
  have h2 : 0 ≤ L.sc.b / szlStar L := div_nonneg (by linarith) h0
  have h3 : L.sc.b' ≤ szlStar L := by linarith [h.1]
  exact (mul_le_mul_of_nonneg_left h3 (by linarith)).trans h1

theorem small_le (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) :
    L.etaSz ≤ L.sc.w'' D.R.n ∧ (D.R.k : ℝ) * D.R.N D.R.m ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' / 2 := by
  have hb' := b'_pos L
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have he : L.etaSz ≤ L.sc.w'' D.R.n :=
    (le_mul_of_one_le_left L.etaSz_pos.le (one_le_mul_of_one_le_of_one_le hm (by linarith))).trans P.mteta
  refine ⟨he, ?_, ?_⟩
  · have h1 := P.h0_ge.2.2.2.2.1
    have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
    obtain ⟨r1, r2⟩ := ranks_le D
    have hN : (1 : ℝ) ≤ D.R.N D.R.m := by linarith
    have h3 : (D.R.k : ℝ) * D.R.N D.R.m ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
    have h4 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have h5 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  · unfold Scale.w''
    refine div_le_div_of_nonneg_left hb'.le (by norm_num) ?_
    nlinarith [one_le_n D]

theorem wj_false_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (t : HH D) : wj D j (tauPl D (false, t)) ≤ 9 / 4 * L.sc.b' := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hR, hB, -⟩ := h
  obtain ⟨e1, -, e3⟩ := small_le P hx
  have hb' := b'_pos L
  by_cases ht : t ∈ D.host.TT
  · have a2 := (L.win_top j h1 h2 _ ⟨t, ht⟩ (eTau_false D t)).2
    have a4 := bT_le hLa hR hB ⟨t, ht⟩
    have a6 : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
    linarith
  · have a2 := (L.win_thin j h1 h2 _ ⟨(D.eTau _).2, false_not_top ht, false_not_thick D t⟩).2
    linarith

theorem wj_true_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (t : HH D) : wj D j (tauPl D (true, t)) ≤ L.sc.b + L.etaSz + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
  obtain ⟨e1, -, e3⟩ := small_le P hx
  have hb' := b'_pos L
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [b'_Sc_le hS, L.Sc_pos]
  by_cases hc : (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces
  · exact (L.win_thick j h1 h2 _ hc).2
  · have a2 := (L.win_thin j h1 h2 _ ⟨(D.eTau _).2, true_not_top D t, hc⟩).2
    linarith

theorem ctD_nonneg (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : HH D) : 0 ≤ ctD D u j t := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk := D.R.m_add_three_le_k
  have hp : ∀ τ, ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), 0 ≤ nuRow D u (i + 1) τ r :=
    fun τ r hr => (RowWeightLemmas.nuRow_pos D u i j2 τ r (Finset.mem_range.1 hr)).le
  have m0 : 0 ∈ Finset.range (D.R.N (i + 1 - 1)) := Finset.mem_range.2 (by unfold Ranks.N; omega)
  have m1 : 1 ∈ Finset.range (D.R.N (i + 1 - 1)) := Finset.mem_range.2 (by unfold Ranks.N; omega)
  have a1 := Finset.single_le_sum (hp (tauPl D (false, t))) m0
  have a2 := hp (tauPl D (false, t)) 0 m0
  have a3 := hp (tauPl D (false, t)) 1 m1
  have a4 := hp (tauPl D (true, t)) 0 m0
  unfold ctD nuAbs
  split_ifs <;> linarith

theorem ctD_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (t : HH D) :
    ctD D u j t ≤ (if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b' := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  obtain ⟨e1, e2, e3⟩ := small_le P hx
  have e4 := P.kS_le
  have e5 := P.mteta
  have hb' := b'_pos L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have hN : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have e6 : L.Sc ≤ L.sc.w'' D.R.n := by nlinarith
  have e7 : (D.R.N D.R.m : ℝ) ≤ L.sc.w'' D.R.n := by nlinarith
  have w0 := (wj_bounds h hx (i + 1) j1 j2 (tauPl D (false, t))).1
  have w1 := wj_false_le h P hx (i + 1) j1 j2 t
  have w2 := wj_true_le h P hx (i + 1) j1 j2 t
  have w3 : (D.R.k : ℝ) * wj D (i + 1) (tauPl D (false, t)) ≤ D.R.k * (9 / 4 * L.sc.b') :=
    mul_le_mul_of_nonneg_left w1 (by linarith)
  have w4 : 5 * L.sc.b' ≤ D.R.k * L.sc.b' := mul_le_mul_of_nonneg_right hk' hb'.le
  have a := (abs_le.1 (nuAbs_place P u i j2 _ w0)).2
  unfold ctD
  by_cases ht : t ∈ D.host.TT
  · simp only [if_pos ht]
    rw [topWt_top L (t := ⟨t, ht⟩) (eTau_false D t)] at a
    have b1 := (head_row u i j2 (tauPl D (false, t)) 0 (by omega)).2
    rw [D.hcW_first u _ (by omega), (L.top_u _ ⟨t, ht⟩ (by omega) (eTau_false D t)).1] at b1
    have b2 := (head_row u i j2 (tauPl D (false, t)) 1 (by omega)).1
    have b3 := (L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)).2
    have b4 := (head_row u i j2 (tauPl D (true, t)) 0 (by omega)).1
    rw [D.hcW_first u _ (by omega)] at b4
    have b5 := P.cloud_place_bound (tauPl D (true, t)) (by omega) (true_not_top D t)
    have b6 := (L.cloud_v (tauPl D (true, t)) ⟨0, by omega⟩).2
    push_cast at b5
    linarith
  · simp only [if_neg ht]
    rw [topWt_off L (false_not_top ht)] at a
    linarith

theorem card_HH (D : D7) : (Fintype.card (HH D) : ℝ) = D.R.n := by
  have : Fintype.card (HH D) = D.R.n := D.R.card_A
  exact_mod_cast this

theorem f_eq (D : D7) : (D.R.f : ℝ) = 2 * D.R.n := by
  unfold Ranks.f
  push_cast
  ring

theorem sum_ctD_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (hj : j ∈ SizeData₂.lifts D)
    (u : D.what₂.Word) :
    ∑ t : HH D, ctD D u j t ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b + 2 * (D.R.f : ℝ) * D.R.k * L.sc.b' := by
  refine (Finset.sum_le_sum fun t _ => ctD_le h P hx u j hj t).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, card_HH, f_eq]
  ring

theorem FRamD_bounds (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    -((D.R.f : ℝ) * D.R.k * L.sc.b') ≤ FRamD D j ∧ FRamD D j ≤ 0 := by
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  have hk := one_le_k D
  have hn := one_le_n D
  have hb' := b'_pos L
  have h0 : 0 ≤ ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) :=
    Finset.sum_nonneg fun t _ => le_min (wj_bounds h hx j j1 j2 _).1 (wj_bounds h hx j j1 j2 _).1
  have h1 : ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) ≤ D.R.n * (9 / 4 * L.sc.b') := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun t _ =>
      (min_le_left _ _).trans (wj_false_le h P hx j j1 j2 t)).trans (le_of_eq ?_)
    rw [Finset.card_univ, nsmul_eq_mul, card_HH]
  have h2 : ((D.R.k : ℝ) - 1) / 2 * ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t)) ≤
      D.R.k / 2 * (D.R.n * (9 / 4 * L.sc.b')) := mul_le_mul (by linarith) h1 h0 (by linarith)
  have h3 : 0 ≤ (D.R.n : ℝ) * D.R.k * L.sc.b' := by positivity
  unfold FRamD
  rw [f_eq]
  exact ⟨by linarith, mul_nonpos_of_nonpos_of_nonneg (by linarith) h0⟩

theorem abs_EatD_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    |EatD D j| ≤ (D.host.TT.card : ℝ) * L.sc.b + (D.R.f : ℝ) * D.R.k * L.sc.b' := by
  obtain ⟨a1, a2⟩ := FRamD_bounds h P hx j hj
  have a3 := Finset.sup'_le (⟨D.u₀, Finset.mem_univ _⟩ : (Finset.univ : Finset D.what₂.Word).Nonempty)
    (fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) fun u _ => sum_ctD_le h P hx j hj u
  have a4 := (Finset.sum_nonneg fun t _ => ctD_nonneg D.u₀ j hj t).trans
    (Finset.le_sup' (fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) (Finset.mem_univ D.u₀))
  have a5 : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b := mul_nonneg (Nat.cast_nonneg _) (by linarith [one_le_b L])
  unfold EatD
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.RamifiedLoss

end
