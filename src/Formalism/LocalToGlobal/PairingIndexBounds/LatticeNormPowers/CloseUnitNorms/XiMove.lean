import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.CloseUnitNorms.TestVectorMemSchwartzBruhat

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Places

variable (D : D7)

def cjK : D.host.K →+* D.host.K :=
  ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E)).codRestrict D.host.K
    (fun a => conj_mem D a.2)

theorem cjK_cjK (a : D.host.K) : cjK D (cjK D a) = a := Subtype.ext (conj_conj D _)

def fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

theorem fK_cjK (a : D.host.K) : fK D (cjK D a) = starRingEnd ℂ (fK D a) :=
  Formalism.BasicNotions.Examples₂.emb_conj _ _ _

variable {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def tK : D.host.K →+* ℂ_[p] := (Lp D lam).comp (algebraMap D.host.K D.host.E)

def tKc : D.host.K →+* ℂ_[p] := (tK D lam).comp (cjK D)

theorem tK_apply (a : D.host.K) : tK D lam a = Lp D lam (a : D.host.E) := rfl

theorem tKc_apply (a : D.host.K) : tKc D lam a = Lp D lam (D.host.conj (a : D.host.E)) := rfl

theorem tKc_cjK (a : D.host.K) : tKc D lam (cjK D a) = tK D lam a := by
  show tK D lam (cjK D (cjK D a)) = _
  rw [cjK_cjK]

theorem tK_cjK (a : D.host.K) : tK D lam (cjK D a) = tKc D lam a := rfl

def Ip (a : D.host.K) : Prop := ‖tK D lam a‖ ≤ 1 ∧ ‖tKc D lam a‖ ≤ 1

theorem Ip_O (u : 𝓞 D.host.K) : Ip D lam (u : D.host.K) := by
  obtain ⟨u', hu'⟩ := conj_O D u
  refine ⟨norm_Lp_le_one D lam u, ?_⟩
  rw [tKc_apply]
  have := norm_Lp_le_one D lam u'
  rwa [hu'] at this

theorem norm_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

theorem norm_sub_le' {x y : ℂ_[p]} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x - y‖ ≤ C := by
  rw [sub_eq_add_neg]
  exact (norm_max _ _).trans (max_le hx (by rwa [norm_neg]))

theorem norm_add_le' {x y : ℂ_[p]} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (norm_max _ _).trans (max_le hx hy)

theorem locInt (a : D.host.K) (h : Ip D lam a) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : 𝓞 D.host.K, (s : D.host.K) * a = (u : D.host.K) := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.K).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  obtain ⟨e, s, hs, hes⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hy0) p hp.out.ne_one
  have hz : IsIntegral ℤ ((y.natAbs : D.host.K) * a) := by
    rcases Int.natAbs_eq y with h' | h'
    · have : (y.natAbs : D.host.K) * a = y • a := by
        rw [zsmul_eq_mul]; congr 1; conv_rhs => rw [h']
        simp
      rw [this]; exact hy
    · have : (y.natAbs : D.host.K) * a = -(y • a) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1; conv_rhs => rw [h']
        simp
      rw [this]; exact hy.neg
  have hsc : Nat.Coprime s p := ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hs).symm
  set z : 𝓞 D.host.K := ⟨(y.natAbs : D.host.K) * a, hz⟩ with hzdef
  have hzE : oE D z = (p : D.host.E) ^ e * ((s : D.host.E) * (a : D.host.E)) := by
    show (((y.natAbs : D.host.K) * a : D.host.K) : D.host.E) = _
    rw [hes]; push_cast; ring
  have hb : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ‖(p : ℂ_[p]) ^ e * ((s : ℂ_[p]) * x)‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
    intro x hx
    rw [norm_mul, norm_mul, normC_p_pow, normC_nat_coprime hsc, one_mul]
    calc _ ≤ (p : ℝ) ^ (-(e : ℤ)) * 1 := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = _ := mul_one _
  obtain ⟨u, hu⟩ := lemT D lam z (le_refl e)
    (by simp only [hzE, map_mul, map_pow, map_natCast]; exact hb _ h.1)
    (by simp only [hzE, map_mul, map_pow, map_natCast]; exact hb _ h.2)
  refine ⟨s, hsc, u, ?_⟩
  apply (algebraMap D.host.K D.host.E).injective
  have hp0E : (p : D.host.E) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  apply mul_left_cancel₀ hp0E
  show (p : D.host.E) ^ e * (((s : D.host.K) * a : D.host.K) : D.host.E) = (p : D.host.E) ^ e * oE D u
  rw [← hu, hzE]; push_cast; ring

theorem locIntVec {ι : Type*} [Fintype ι] (a : ι → D.host.K) (h : ∀ i, Ip D lam (a i)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : ι → 𝓞 D.host.K, ∀ i, (s : D.host.K) * a i = (u i : D.host.K) := by
  classical
  choose s hs u hu using fun i => locInt D lam (a i) (h i)
  refine ⟨∏ i, s i, Nat.Coprime.prod_left (fun i _ => hs i),
    fun i => ((∏ j ∈ Finset.univ.erase i, s j : ℕ) : 𝓞 D.host.K) * u i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  push_cast
  rw [mul_assoc, hu i]

theorem mem_of_coprime {V : Type*} [AddCommGroup V] [Module ℂ V] (S : AddSubgroup V) {x : V} {s N : ℕ}
    (hs : Nat.Coprime s p) (h1 : (s : ℂ) • x ∈ S) (h2 : ((p : ℂ) ^ N) • x ∈ S) : x ∈ S := by
  have hcop : IsCoprime (s : ℤ) ((p ^ N : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hs.pow_right N)
  obtain ⟨u, v, huv⟩ := hcop
  have huvC : (u : ℂ) * s + (v : ℂ) * (p : ℂ) ^ N = 1 := by exact_mod_cast huv
  have : x = u • ((s : ℂ) • x) + v • (((p : ℂ) ^ N) • x) := by
    rw [← Int.cast_smul_eq_zsmul ℂ u, ← Int.cast_smul_eq_zsmul ℂ v, smul_smul, smul_smul, ← add_smul, huvC,
      one_smul]
  rw [this]
  exact add_mem (zsmul_mem h1 u) (zsmul_mem h2 v)

end Places

section Approx

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem idem_norm {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) :
    ‖tK D lam (ε : D.host.K) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) ∧ ‖tK D lam (ε : D.host.K)‖ = 1 ∧
      ‖tKc D lam (ε : D.host.K)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨h1, h2⟩ := hId
  rw [lamC_phi_zero_eq] at h1 h2
  exact ⟨h1, norm_eq_one_of_close (lt_of_le_of_lt h1 (pzpow_lt_one hm)), h2⟩

theorem approxO {n : ℕ} {ε : 𝓞 D.host.K} (hId : IsIdem D lam (2 * n + 2) ε) (μ : 𝓞 D.host.K) :
    ∃ c0 : ℤ, ‖tKc D lam (μ : D.host.K) - c0‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨c0, w, hw⟩ := alg_step D lam ε n hId μ
  obtain ⟨-, he, -⟩ := idem_norm D lam (by omega) hId
  refine ⟨c0, ?_⟩
  have h := congrArg (Lp D lam) hw
  rw [map_mul, map_add, map_mul, map_mul, map_intCast, map_pow, map_natCast] at h
  have h2 : tK D lam (ε : D.host.K) * (tKc D lam (μ : D.host.K) - c0) = (p : ℂ_[p]) ^ n * Lp D lam (oE D w) := by
    rw [tK_apply, tKc_apply]
    linear_combination h
  have h3 := congrArg norm h2
  rw [norm_mul, he, one_mul, norm_mul, normC_p_pow] at h3
  rw [h3]
  calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left (norm_Lp_le_one D lam w) (by positivity)
    _ = _ := mul_one _

theorem approxKc {n : ℕ} {ε : 𝓞 D.host.K} (hId : IsIdem D lam (2 * n + 2) ε) (a : D.host.K)
    (ha : Ip D lam a) : ∃ m : Fin (p ^ n), ‖tKc D lam a - ((m : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨s, hs, u, hu⟩ := locInt D lam a ha
  obtain ⟨c0, hc0⟩ := approxO D lam hId u
  have hcop : IsCoprime (s : ℤ) ((p ^ n : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr (hs.pow_right n)
  obtain ⟨x, y, hxy⟩ := hcop
  have hpn : (0 : ℤ) < (p ^ n : ℕ) := by exact_mod_cast pow_pos hp.out.pos n
  set m : ℤ := (c0 * x) % ((p ^ n : ℕ) : ℤ) with hm
  have hm0 : 0 ≤ m := Int.emod_nonneg _ hpn.ne'
  have hm1 : m < (p ^ n : ℕ) := Int.emod_lt_of_pos _ hpn
  refine ⟨⟨m.toNat, by omega⟩, ?_⟩
  have hcast : ((m.toNat : ℕ) : ℂ_[p]) = (m : ℂ_[p]) := by
    have : (((m.toNat : ℕ) : ℤ) : ℂ_[p]) = (m : ℂ_[p]) := by rw [Int.toNat_of_nonneg hm0]
    rw [← this, Int.cast_natCast]
  show ‖tKc D lam a - ((m.toNat : ℕ) : ℂ_[p])‖ ≤ _
  rw [hcast]
  have hq : ((p ^ n : ℕ) : ℤ) ∣ c0 * x - m :=
    ⟨c0 * x / ((p ^ n : ℕ) : ℤ), by
      have := Int.mul_ediv_add_emod (c0 * x) ((p ^ n : ℕ) : ℤ)
      rw [hm]; linarith⟩
  obtain ⟨q, hq⟩ := hq
  have hs1 := normC_nat_coprime (p := p) hs
  have hxyC : (x : ℂ_[p]) * s + (y : ℂ_[p]) * (p : ℂ_[p]) ^ n = 1 := by exact_mod_cast hxy
  have hqC : (c0 : ℂ_[p]) * x - m = (p : ℂ_[p]) ^ n * q := by exact_mod_cast hq
  have huC : (s : ℂ_[p]) * tKc D lam a = tKc D lam (u : D.host.K) := by
    rw [← hu, map_mul, map_natCast]
  have key : (s : ℂ_[p]) * (tKc D lam a - m) =
      (tKc D lam (u : D.host.K) - c0) + (p : ℂ_[p]) ^ n * ((c0 : ℂ_[p]) * y + s * q) := by
    linear_combination huC - (c0 : ℂ_[p]) * hxyC + (s : ℂ_[p]) * hqC
  have h3 := congrArg norm key
  rw [norm_mul, hs1, one_mul] at h3
  rw [h3]
  refine norm_add_le' hc0 ?_
  rw [norm_mul, normC_p_pow]
  have : ‖(c0 : ℂ_[p]) * y + s * q‖ ≤ 1 := by
    have e : (c0 : ℂ_[p]) * y + s * q = ((c0 * y + s * q : ℤ) : ℂ_[p]) := by push_cast; ring
    rw [e]; exact normC_int_le_one _
  calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

theorem Ip_cjK {a : D.host.K} (ha : Ip D lam a) : Ip D lam (cjK D a) :=
  ⟨by rw [tK_cjK]; exact ha.2, by rw [tKc_cjK]; exact ha.1⟩

theorem approxK {n : ℕ} {ε : 𝓞 D.host.K} (hId : IsIdem D lam (2 * n + 2) ε) (a : D.host.K)
    (ha : Ip D lam a) : ∃ m : Fin (p ^ n), ‖tK D lam a - ((m : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨m, hm⟩ := approxKc D lam hId (cjK D a) (Ip_cjK D lam ha)
  exact ⟨m, by rwa [tKc_cjK] at hm⟩

theorem idem_step {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) :
    IsIdem D lam (m + 1) (3 * ε ^ 2 - 2 * ε ^ 3) := by
  obtain ⟨h1, he, h2⟩ := idem_norm D lam hm hId
  have hpp : (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
    apply zpow_le_zpow_right₀
    · exact_mod_cast hp.out.one_lt.le
    · push_cast; omega
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(m : ℤ)) := by positivity
  have hc1 : ‖tKc D lam (ε : D.host.K)‖ ≤ 1 := (Ip_O D lam ε).2
  constructor
  · rw [lamC_phi_zero_eq]
    have e : Lp D lam (((3 * ε ^ 2 - 2 * ε ^ 3 : 𝓞 D.host.K) : D.host.K) : D.host.E) - 1 =
        (tK D lam (ε : D.host.K) - 1) * (tK D lam (ε : D.host.K) - 1) *
          (((-2 : ℤ) : ℂ_[p]) * tK D lam (ε : D.host.K) - ((1 : ℤ) : ℂ_[p])) := by
      have ht : tK D lam (algebraMap (𝓞 D.host.K) D.host.K ε) = tK D lam (ε : D.host.K) := rfl
      change (tK D lam) (algebraMap (𝓞 D.host.K) D.host.K (3 * ε ^ 2 - 2 * ε ^ 3)) - 1 = _
      simp only [map_sub, map_mul, map_pow, map_ofNat, ht]
      push_cast
      ring
    rw [e, norm_mul, norm_mul]
    have h3 : ‖((-2 : ℤ) : ℂ_[p]) * tK D lam (ε : D.host.K) - ((1 : ℤ) : ℂ_[p])‖ ≤ 1 := by
      refine norm_sub_le' ?_ (normC_int_le_one _)
      rw [norm_mul, he, mul_one]; exact normC_int_le_one _
    calc _ ≤ (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul (mul_le_mul h1 h1 (norm_nonneg _) hpos) h3 (norm_nonneg _) (by positivity)
      _ ≤ _ := by rw [mul_one]; exact hpp
  · rw [lamC_phi_zero_eq]
    have e : Lp D lam (D.host.conj (((3 * ε ^ 2 - 2 * ε ^ 3 : 𝓞 D.host.K) : D.host.K) : D.host.E)) =
        tKc D lam (ε : D.host.K) * tKc D lam (ε : D.host.K) *
          (((3 : ℤ) : ℂ_[p]) - ((2 : ℤ) : ℂ_[p]) * tKc D lam (ε : D.host.K)) := by
      have ht : tKc D lam (algebraMap (𝓞 D.host.K) D.host.K ε) = tKc D lam (ε : D.host.K) := rfl
      change (tKc D lam) (algebraMap (𝓞 D.host.K) D.host.K (3 * ε ^ 2 - 2 * ε ^ 3)) = _
      simp only [map_sub, map_mul, map_pow, map_ofNat, ht]
      push_cast
      ring
    rw [e, norm_mul, norm_mul]
    have h3 : ‖((3 : ℤ) : ℂ_[p]) - ((2 : ℤ) : ℂ_[p]) * tKc D lam (ε : D.host.K)‖ ≤ 1 := by
      refine norm_sub_le' (normC_int_le_one _) ?_
      rw [norm_mul]
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (normC_int_le_one _) hc1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    calc _ ≤ (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul (mul_le_mul h2 h2 (norm_nonneg _) hpos) h3 (norm_nonneg _) (by positivity)
      _ ≤ _ := by rw [mul_one]; exact hpp

theorem idem_all {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) (M : ℕ) :
    ∃ η : 𝓞 D.host.K, IsIdem D lam (m + M) η := by
  induction M with
  | zero => exact ⟨ε, hId⟩
  | succ M ih =>
    obtain ⟨η, hη⟩ := ih
    exact ⟨_, idem_step D lam (m := m + M) (by omega) hη⟩

end Approx

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Bounds

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def Bd (a : D.host.K) (e1 e2 : ℤ) : Prop :=
  ‖tK D lam a‖ ≤ (p : ℝ) ^ e1 ∧ ‖tKc D lam a‖ ≤ (p : ℝ) ^ e2

variable {D lam}

theorem Bd.ip {a : D.host.K} (h : Bd D lam a 0 0) : Ip D lam a := by
  simpa [Bd, Ip] using h

theorem Ip.bd {a : D.host.K} (h : Ip D lam a) : Bd D lam a 0 0 := by
  simpa [Bd, Ip] using h

theorem pz_mono {e f : ℤ} (h : e ≤ f) : (p : ℝ) ^ e ≤ (p : ℝ) ^ f :=
  zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) h

theorem pz_pos (e : ℤ) : (0 : ℝ) < (p : ℝ) ^ e := zpow_pos (by exact_mod_cast hp.out.pos) e

theorem Bd.mono {a : D.host.K} {e1 e2 f1 f2 : ℤ} (h : Bd D lam a e1 e2) (h1 : e1 ≤ f1) (h2 : e2 ≤ f2) :
    Bd D lam a f1 f2 := ⟨h.1.trans (pz_mono h1), h.2.trans (pz_mono h2)⟩

theorem Bd.mul {a b : D.host.K} {e1 e2 f1 f2 : ℤ} (ha : Bd D lam a e1 e2) (hb : Bd D lam b f1 f2) :
    Bd D lam (a * b) (e1 + f1) (e2 + f2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rw [map_mul, norm_mul, zpow_add₀ hp0]
    exact mul_le_mul ha.1 hb.1 (norm_nonneg _) (pz_pos _).le
  · rw [map_mul, norm_mul, zpow_add₀ hp0]
    exact mul_le_mul ha.2 hb.2 (norm_nonneg _) (pz_pos _).le

theorem Bd.cj {a : D.host.K} {e1 e2 : ℤ} (ha : Bd D lam a e1 e2) : Bd D lam (cjK D a) e2 e1 :=
  ⟨by rw [tK_cjK]; exact ha.2, by rw [tKc_cjK]; exact ha.1⟩

theorem Bd.sub {a b : D.host.K} {e1 e2 : ℤ} (ha : Bd D lam a e1 e2) (hb : Bd D lam b e1 e2) :
    Bd D lam (a - b) e1 e2 :=
  ⟨by rw [map_sub]; exact norm_sub_le' ha.1 hb.1, by rw [map_sub]; exact norm_sub_le' ha.2 hb.2⟩

theorem Bd.sum {ι : Type*} (s : Finset ι) {a : ι → D.host.K} {e1 e2 : ℤ} (ha : ∀ i ∈ s, Bd D lam (a i) e1 e2) :
    Bd D lam (∑ i ∈ s, a i) e1 e2 :=
  ⟨by rw [map_sum]; exact norm_sum_le' _ _ (pz_pos _).le fun i hi => (ha i hi).1,
   by rw [map_sum]; exact norm_sum_le' _ _ (pz_pos _).le fun i hi => (ha i hi).2⟩

theorem Bd.nat (m : ℕ) : Bd D lam (m : D.host.K) 0 0 := by
  constructor <;> rw [map_natCast, zpow_zero] <;>
    exact (by simpa using normC_int_le_one (p := p) (m : ℤ))

theorem Bd.ppow (n : ℕ) : Bd D lam ((p : D.host.K) ^ n) (-(n : ℤ)) (-(n : ℤ)) := by
  constructor <;> rw [map_pow, map_natCast, normC_p_pow]

theorem Bd.ppow_inv (n : ℕ) : Bd D lam (((p : D.host.K) ^ n)⁻¹) (n : ℤ) (n : ℤ) := by
  constructor <;> rw [map_inv₀, map_pow, map_natCast, norm_inv, normC_p_pow, zpow_neg, inv_inv]

theorem Bd.idem {m : ℕ} (hm : 1 ≤ m) {ε : 𝓞 D.host.K} (hId : IsIdem D lam m ε) :
    Bd D lam (ε : D.host.K) 0 (-(m : ℤ)) := by
  obtain ⟨-, h1, h2⟩ := idem_norm D lam hm hId
  exact ⟨by rw [h1, zpow_zero], h2⟩

end Bounds

section LBs

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

variable (D cc δ) in

def cv {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ξ : Fin r → D.host.K) : VC D N N' :=
  ∑ i, fK D (ξ i) • ee D cc δ b i

theorem cv_sub {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ξ ξ' : Fin r → D.host.K) :
    cv D cc δ b (ξ - ξ') = cv D cc δ b ξ - cv D cc δ b ξ' := by
  simp only [cv, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem cv_smul {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : D.host.K) (ξ : Fin r → D.host.K) :
    cv D cc δ b (fun i => a * ξ i) = fK D a • cv D cc δ b ξ := by
  simp only [cv, map_mul, mul_smul, Finset.smul_sum]

theorem cv_change {r : ℕ} {f g : Fin r → Matrix (Fin N') (Fin N) D.host.E} {c : Fin r → Fin r → D.host.K}
    (hc : ∀ j, ee D cc δ g j = cv D cc δ f (fun i => c i j)) (ζ : Fin r → D.host.K) :
    cv D cc δ g ζ = cv D cc δ f (fun i => ∑ j, c i j * ζ j) := by
  simp only [cv, hc, Finset.smul_sum, map_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

variable (D cc δ) in

structure LB (p : ℕ) (La' : AddSubgroup (VC D N N')) {r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop where
  int : ∀ x ∈ La', ∀ y ∈ La', ∃ k : ℤ, (Hf D (tor0 D cc δ) x y).im = k
  sd : ∀ v, (∀ y ∈ La', ∃ k : ℤ, (Hf D (tor0 D cc δ) v y).im = k) → v ∈ La'
  ok : ∀ (κ : 𝓞 D.host.K) (v : VC D N N'), v ∈ La' → fK D (κ : D.host.K) • v ∈ La'
  mem : ∀ i, ee D cc δ b i ∈ La'
  loc : ∀ v ∈ La', ∃ s : ℕ, Nat.Coprime s p ∧ ∃ κ : Fin r → 𝓞 D.host.K,
    (s : ℂ) • v = cv D cc δ b (fun i => (κ i : D.host.K))
  li : ∀ ξ : Fin r → D.host.K, cv D cc δ b ξ = 0 → ξ = 0

variable {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {La' : AddSubgroup (VC D N N')} {r : ℕ}
  {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}

theorem LB.cvO (h : LB D cc δ p La' b) (u : Fin r → 𝓞 D.host.K) :
    cv D cc δ b (fun i => (u i : D.host.K)) ∈ La' :=
  sum_mem fun i _ => h.ok (u i) _ (h.mem i)

theorem LB.coord (h : LB D cc δ p La' b) {v : VC D N N'} (hv : v ∈ La') :
    ∃ ζ : Fin r → D.host.K, v = cv D cc δ b ζ ∧ ∀ j, Ip D lam (ζ j) := by
  obtain ⟨s, hs, κ, hκ⟩ := h.loc v hv
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp.out.ne_one (by simpa using hs)
  have hsK : (s : D.host.K) ≠ 0 := by exact_mod_cast hs0
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  refine ⟨fun j => (s : D.host.K)⁻¹ * (κ j : D.host.K), ?_, fun j => ?_⟩
  · rw [cv_smul, ← hκ, map_inv₀, map_natCast, smul_smul, inv_mul_cancel₀ hsC, one_smul]
  · have h1 := normC_nat_coprime (p := p) hs
    obtain ⟨h2, h3⟩ := Ip_O D lam (κ j)
    constructor
    · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, h1, inv_one, one_mul]; exact h2
    · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, h1, inv_one, one_mul]; exact h3

theorem LB.memOf (h : LB D cc δ p La' b) {ξ : Fin r → D.host.K} (hξ : ∀ i, Ip D lam (ξ i)) {Np : ℕ}
    (hN : ((p : ℂ) ^ Np) • cv D cc δ b ξ ∈ La') : cv D cc δ b ξ ∈ La' := by
  obtain ⟨s, hs, u, hu⟩ := locIntVec D lam ξ hξ
  refine mem_of_coprime La' hs ?_ hN
  have : (s : ℂ) • cv D cc δ b ξ = cv D cc δ b (fun i => (u i : D.host.K)) := by
    simp_rw [← hu]
    rw [cv_smul, map_natCast]
  rw [this]
  exact h.cvO u

theorem LB.ipOf (h : LB D cc δ p La' b) {ξ : Fin r → D.host.K} (hξ : cv D cc δ b ξ ∈ La') (i : Fin r) :
    Ip D lam (ξ i) := by
  obtain ⟨ζ, h1, h2⟩ := h.coord lam hξ
  have : ξ - ζ = 0 := h.li _ (by rw [cv_sub, h1, sub_self])
  rw [sub_eq_zero.mp this]
  exact h2 i

end LBs

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section Dual

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
variable {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {r : ℕ}

theorem dual {A B : AddSubgroup (VC D N N')} {f g : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hA : LB D cc δ p A f) (hB : LB D cc δ p B g) {m0 : ℕ} (hm0 : 1 ≤ m0) {ε : 𝓞 D.host.K}
    (hId : IsIdem D lam m0 ε) {Np : ℕ} (hcom : ∀ v ∈ B, ((p : ℂ) ^ Np) • v ∈ A)
    {c d : Fin r → Fin r → D.host.K} (hc : ∀ j, ee D cc δ g j = cv D cc δ f (fun i => c i j))
    (hd : ∀ i, ee D cc δ f i = cv D cc δ g (fun j => d j i)) (t : ℕ)
    (hbd : ∀ i j, ‖tKc D lam (c i j)‖ ≤ (p : ℝ) ^ (t : ℤ)) (i j : Fin r) :
    ‖tK D lam (d j i)‖ ≤ (p : ℝ) ^ (t : ℤ) := by
  have hp0K : (p : D.host.K) ^ Np ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hc1 : ∀ i j, Bd D lam (c i j) Np t := by
    intro i j
    have hmem : cv D cc δ f (fun i => (p : D.host.K) ^ Np * c i j) ∈ A := by
      rw [cv_smul, ← hc, map_pow, map_natCast]; exact hcom _ (hB.mem j)
    have h2 := (Bd.ppow_inv (D := D) (lam := lam) Np).mul (hA.ipOf lam hmem i).bd
    refine ⟨?_, hbd i j⟩
    have e : ((p : D.host.K) ^ Np)⁻¹ * ((p : D.host.K) ^ Np * c i j) = c i j := by field_simp
    rw [e] at h2
    simpa using h2.1
  obtain ⟨η, hη⟩ := idem_all D lam hm0 hId Np
  obtain ⟨η', hη'⟩ := conj_O D η
  have hηK : (η' : D.host.K) = cjK D (η : D.host.K) := Subtype.ext hη'
  have hbη := Bd.idem (m := m0 + Np) (by omega) hη
  have hbη' : Bd D lam (η' : D.host.K) (-((m0 + Np : ℕ) : ℤ)) 0 := hηK ▸ hbη.cj
  have hκ : (((p : 𝓞 D.host.K) ^ t * η : 𝓞 D.host.K) : D.host.K) = (p : D.host.K) ^ t * (η : D.host.K) := by
    push_cast; rfl
  have hκ' : (((p : 𝓞 D.host.K) ^ t * η' : 𝓞 D.host.K) : D.host.K) = (p : D.host.K) ^ t * (η' : D.host.K) := by
    push_cast; rfl
  have hx : fK D ((p : D.host.K) ^ t * (η : D.host.K)) • ee D cc δ f i ∈ B := by
    apply hB.sd
    intro v hv
    obtain ⟨ζ, hvζ, hζ⟩ := hB.coord lam hv
    have e1 : Hf D (tor0 D cc δ) (fK D ((p : D.host.K) ^ t * (η : D.host.K)) • ee D cc δ f i) v =
        Hf D (tor0 D cc δ) (ee D cc δ f i) (fK D ((p : D.host.K) ^ t * (η' : D.host.K)) • v) := by
      rw [Hf_smul_left, Hf_smul_right]
      congr 1
      rw [hηK, map_mul, map_mul, map_mul, fK_cjK, Complex.conj_conj, map_pow, map_pow, map_natCast,
        Complex.conj_natCast]
    rw [e1]
    apply hA.int _ (hA.mem i)
    have e2 : fK D ((p : D.host.K) ^ t * (η' : D.host.K)) • v =
        cv D cc δ f (fun i' => ((p : D.host.K) ^ t * (η' : D.host.K)) * ∑ j', c i' j' * ζ j') := by
      rw [cv_smul, ← cv_change hc, ← hvζ]
    rw [e2]
    apply hA.memOf lam (Np := Np)
    · intro i'
      have h3 : Bd D lam (∑ j', c i' j' * ζ j') (Np + 0) (t + 0) :=
        Bd.sum _ fun j' _ => (hc1 i' j').mul (hζ j').bd
      exact ((((Bd.ppow t).mul hbη').mul h3).mono (by push_cast; omega) (by omega)).ip
    · rw [← e2, smul_comm, ← hκ']
      exact hA.ok _ _ (hcom _ hv)
  rw [hd, ← cv_smul] at hx
  have h4 := (hB.ipOf lam hx j).1
  obtain ⟨-, h5, -⟩ := idem_norm D lam (m := m0 + Np) (by omega) hη
  rw [map_mul, map_mul, norm_mul, norm_mul, h5, mul_one, map_pow, map_natCast, normC_p_pow] at h4
  have hpos := pz_pos (p := p) (t : ℤ)
  calc ‖tK D lam (d j i)‖ = (p : ℝ) ^ (t : ℤ) * ((p : ℝ) ^ (-(t : ℤ)) * ‖tK D lam (d j i)‖) := by
        rw [← mul_assoc, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp
    _ ≤ (p : ℝ) ^ (t : ℤ) * 1 := mul_le_mul_of_nonneg_left h4 hpos.le
    _ = _ := mul_one _

end Dual

section Rat

variable {p : ℕ} [hp : Fact p.Prime] {r : ℕ}

theorem norm_zc (a : ℤ_[p]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [show (algebraMap ℚ_[p] ℂ_[p]) (a : ℚ_[p]) = ((a : ℚ_[p]) : ℂ_[p]) from rfl, PadicComplex.norm_extends']
  rfl

end Rat

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section ZC

variable {p : ℕ} [hp : Fact p.Prime]

def zcH : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem norm_zcH (a : ℤ_[p]) : ‖zcH a‖ = ‖a‖ := norm_zc a

theorem norm_zcH_le_one (a : ℤ_[p]) : ‖zcH a‖ ≤ 1 := by rw [norm_zcH]; exact PadicInt.norm_le_one a

end ZC

section Ctxs

variable {N N' : ℕ}

structure Ctx (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (La₁ La : AddSubgroup (VC D N N')) {r : ℕ} (b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (c d : Fin r → Fin r → D.host.K) (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (Np : ℕ) : Prop where
  h₁ : LB D cc δ p La₁ b₁
  h : LB D cc δ p La b
  com1 : ∀ v ∈ La, ((p : ℂ) ^ Np) • v ∈ La₁
  com2 : ∀ v ∈ La₁, ((p : ℂ) ^ Np) • v ∈ La
  hc : ∀ j, ee D cc δ b j = cv D cc δ b₁ (fun i => c i j)
  hd : ∀ i, ee D cc δ b₁ i = cv D cc δ b (fun j => d j i)
  cb : ∀ i j, ‖tKc D lam (c i j)‖ ≤ 1
  id : IsIdem D lam (2 * n + 2) ε
  fm : FactorsMod n Φ
  phi1 : ∀ a, (∃ x : Fin r → ℤ_[p], ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j)) → Φ a = 1
  phi0 : ∀ a, (¬ ∃ x : Fin r → ℤ_[p], ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j)) → Φ a = 0

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [hp : Fact p.Prime] {lam : Qbar →+* ℂ_[p]}
  {La₁ La : AddSubgroup (VC D N N')} {r : ℕ} {b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
  {c d : Fin r → Fin r → D.host.K} {n : ℕ} {ε : 𝓞 D.host.K} {Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ} {Np : ℕ}

theorem Ctx.dc (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (ζ : Fin r → D.host.K) (j : Fin r) :
    ∑ i, d j i * ∑ l, c i l * ζ l = ζ j := by
  have := X.h.li ((fun j => ∑ i, d j i * ∑ l, c i l * ζ l) - ζ)
    (by rw [cv_sub, ← cv_change X.hd, ← cv_change X.hc, sub_self])
  exact congrFun (sub_eq_zero.mp this) j

theorem Ctx.dcm (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (j l : Fin r) :
    ∑ i, d j i * c i l = if j = l then 1 else 0 := by
  have := X.dc (fun l' => if l' = l then 1 else 0) j
  simpa [mul_ite] using this

theorem Ctx.phi_one (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {a : Fin r → ℤ_[p]}
    (x : Fin r → ℤ_[p]) (hx : ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j)) : Φ a = 1 := X.phi1 a ⟨x, hx⟩

theorem Ctx.of_phi_one (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {a : Fin r → ℤ_[p]}
    (ha : Φ a = 1) : ∃ x : Fin r → ℤ_[p], ∀ i, zcH (a i) = ∑ j, tKc D lam (c i j) * zcH (x j) := by
  by_contra hne
  rw [X.phi0 a hne] at ha
  exact zero_ne_one ha

theorem Ctx.exX (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) :
    ∃ Xm : Fin r → Fin r → ℤ_[p], ∀ i l,
      ∑ j, tKc D lam (c i j) * zcH (Xm j l) = if i = l then (p : ℂ_[p]) ^ n else 0 := by
  have h0 : Φ 0 = 1 := X.phi_one 0 (by intro i; simp)
  have hl : ∀ l : Fin r, ∃ x : Fin r → ℤ_[p], ∀ i,
      zcH ((fun i => if i = l then (p : ℤ_[p]) ^ n else 0 : Fin r → ℤ_[p]) i) =
        ∑ j, tKc D lam (c i j) * zcH (x j) := by
    intro l
    apply X.of_phi_one
    rw [← h0]
    apply X.fm
    intro i
    simp only [Pi.zero_apply, sub_zero]
    split_ifs
    · rw [PadicInt.norm_p_pow]
    · rw [norm_zero]; positivity
  choose x hx using hl
  refine ⟨fun j l => x l j, fun i l => ?_⟩
  rw [← hx l i]
  by_cases hil : i = l <;> simp [hil]

theorem Ctx.dX (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {Xm : Fin r → Fin r → ℤ_[p]}
    (hX : ∀ i l, ∑ j, tKc D lam (c i j) * zcH (Xm j l) = if i = l then (p : ℂ_[p]) ^ n else 0)
    (j l : Fin r) : tKc D lam (d j l) * (p : ℂ_[p]) ^ n = zcH (Xm j l) := by
  have h1 : ∑ i, tKc D lam (d j i) * ∑ j', tKc D lam (c i j') * zcH (Xm j' l) =
      tKc D lam (d j l) * (p : ℂ_[p]) ^ n := by
    simp_rw [hX]
    simp [mul_ite]
  rw [← h1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum, X.dcm]
  simp [apply_ite (tKc D lam)]

theorem Ctx.norm_entry_le_prime_pow (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (j l : Fin r) :
    ‖tKc D lam (d j l)‖ ≤ (p : ℝ) ^ (n : ℤ) := by
  obtain ⟨Xm, hX⟩ := X.exX
  have h := congrArg norm (X.dX hX j l)
  rw [norm_mul, normC_p_pow] at h
  have h2 := norm_zcH_le_one (Xm j l)
  rw [← h] at h2
  calc ‖tKc D lam (d j l)‖ = (‖tKc D lam (d j l)‖ * (p : ℝ) ^ (-(n : ℤ))) * (p : ℝ) ^ (n : ℤ) := by
        rw [mul_assoc, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp
    _ ≤ 1 * (p : ℝ) ^ (n : ℤ) := mul_le_mul_of_nonneg_right h2 (pz_pos _).le
    _ = _ := one_mul _

theorem Ctx.bd_d (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (j i : Fin r) :
    Bd D lam (d j i) 0 n :=
  ⟨by
    have := dual lam X.h₁ X.h (m0 := 2 * n + 2) (by omega) X.id X.com1 X.hc X.hd 0
      (by intro i j; simpa using X.cb i j) i j
    simpa using this, X.norm_entry_le_prime_pow j i⟩

theorem Ctx.bd_c (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) (i j : Fin r) :
    Bd D lam (c i j) n 0 :=
  ⟨dual lam X.h X.h₁ (m0 := 2 * n + 2) (by omega) X.id X.com2 X.hd X.hc n (fun j i => X.norm_entry_le_prime_pow j i) j i,
    by simpa using X.cb i j⟩

end Ctxs

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Xf.XiOneP

section PTs

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def PT (p : ℕ) (S : AddSubgroup V) (x : V) : Prop := ∃ k : ℕ, ((p : ℂ) ^ k) • x ∈ S

theorem pow_smul_mem {p : ℕ} {S : AddSubgroup V} {v : V} (hv : v ∈ S) (k : ℕ) : ((p : ℂ) ^ k) • v ∈ S := by
  have : ((p : ℂ) ^ k) • v = (p ^ k : ℕ) • v := by
    rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
  rw [this]; exact nsmul_mem hv _

theorem PT.of_mem {p : ℕ} {S : AddSubgroup V} {v : V} (hv : v ∈ S) : PT p S v := ⟨0, by simpa using hv⟩

theorem PT.sub {p : ℕ} {S : AddSubgroup V} {x y : V} (hx : PT p S x) (hy : PT p S y) : PT p S (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  have : ((p : ℂ) ^ (a + b)) • (x - y) = ((p : ℂ) ^ b) • (((p : ℂ) ^ a) • x) - ((p : ℂ) ^ a) • (((p : ℂ) ^ b) • y) := by
    rw [smul_sub, smul_smul, smul_smul, pow_add, mul_comm]
  rw [this]
  exact sub_mem (pow_smul_mem ha _) (pow_smul_mem hb _)

theorem PT.trans {p : ℕ} {S S' : AddSubgroup V} {Np : ℕ} (h : ∀ v ∈ S, ((p : ℂ) ^ Np) • v ∈ S') {x : V}
    (hx : PT p S x) : PT p S' x := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨Np + a, by rw [pow_add, mul_smul]; exact h _ ha⟩

end PTs

section Claims

variable {N N' : ℕ}
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [hp : Fact p.Prime] {lam : Qbar →+* ℂ_[p]}
  {La₁ La : AddSubgroup (VC D N N')} {r : ℕ} {b₁ b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
  {c d : Fin r → Fin r → D.host.K} {n : ℕ} {ε : 𝓞 D.host.K} {Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ} {Np : ℕ}

theorem LB.memOf' (h : LB D cc δ p La b) (lam : Qbar →+* ℂ_[p]) {ξ : Fin r → D.host.K}
    (hξ : ∀ i, Ip D lam (ξ i)) (hN : PT p La (cv D cc δ b ξ)) : cv D cc δ b ξ ∈ La := by
  obtain ⟨k, hk⟩ := hN
  exact h.memOf lam hξ hk

variable (D) in

def lyc (p n : ℕ) (ε : 𝓞 D.host.K) (y : Fin r → Fin (p ^ n)) : Fin r → D.host.K :=
  fun i => ((ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹) * ((y i : ℕ) : D.host.K)

theorem bd_q (hId : IsIdem D lam (2 * n + 2) ε) :
    Bd D lam ((ε : D.host.K) * ((p : D.host.K) ^ n)⁻¹) n (-((n : ℤ) + 2)) :=
  ((Bd.idem (by omega) hId).mul (Bd.ppow_inv n)).mono (by omega) (by push_cast; omega)

theorem lyc₂ (hId : IsIdem D lam (2 * n + 2) ε) (y : Fin r → Fin (p ^ n)) (i : Fin r) :
    Bd D lam (lyc D p n ε y i) n (-((n : ℤ) + 2)) :=
  ((bd_q hId).mul (Bd.nat _)).mono (by omega) (by omega)

theorem ly_PT (h : LB D cc δ p La b) (ε : 𝓞 D.host.K) (y : Fin r → Fin (p ^ n)) :
    PT p La (cv D cc δ b (lyc D p n ε y)) := by
  refine ⟨n, ?_⟩
  have hp0 : (p : D.host.K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have := h.cvO (fun j => ε * ((y j : ℕ) : 𝓞 D.host.K))
  have e : (fun j => ((ε * ((y j : ℕ) : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)) =
      fun j => (p : D.host.K) ^ n * lyc D p n ε y j := by
    funext j
    simp only [lyc]
    push_cast
    field_simp
  rw [e, cv_smul, map_pow, map_natCast] at this
  exact this

theorem norm_le_one_of_pow {x : ℂ_[p]} (h : ‖(p : ℂ_[p]) ^ n * x‖ ≤ (p : ℝ) ^ (-(n : ℤ))) : ‖x‖ ≤ 1 := by
  rw [norm_mul, normC_p_pow] at h
  have hpos := pz_pos (p := p) (-(n : ℤ))
  by_contra hlt
  push Not at hlt
  have : (p : ℝ) ^ (-(n : ℤ)) * 1 < (p : ℝ) ^ (-(n : ℤ)) * ‖x‖ := mul_lt_mul_of_pos_left hlt hpos
  linarith

theorem Ctx.onto (X : Ctx D cc δ p lam La₁ La b₁ b c d n ε Φ Np) {q : VC D N N'} (hq : q ∈ La) :
    ∃ y : Fin r → Fin (p ^ n), q - cv D cc δ b₁ (lyc D p n ε y) ∈ La₁ ∧
      cv D cc δ b₁ (lyc D p n ε y) ∈ La := by
  obtain ⟨ζ, hqζ, hζ⟩ := X.h.coord lam hq
  set ξ : Fin r → D.host.K := fun i => ∑ j, c i j * ζ j with hξdef
  have hqξ : q = cv D cc δ b₁ ξ := by rw [hqζ, cv_change X.hc]
  have hξ : ∀ i, Bd D lam (ξ i) n 0 := fun i =>
    (Bd.sum _ fun j _ => (X.bd_c i j).mul (hζ j).bd).mono (by omega) (by omega)
  have hpξ : ∀ i, Ip D lam ((p : D.host.K) ^ n * ξ i) := fun i =>
    (((Bd.ppow n).mul (hξ i)).mono (by omega) (by omega)).ip
  choose y hy using fun i => approxK D lam X.id _ (hpξ i)
  obtain ⟨he1, he, -⟩ := idem_norm D lam (by omega) X.id
  have hp0 : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hρ : ∀ i, Ip D lam ((ξ - lyc D p n ε y) i) := by
    intro i
    constructor
    · apply norm_le_one_of_pow (n := n)
      have e : (p : ℂ_[p]) ^ n * tK D lam ((ξ - lyc D p n ε y) i) =
          (tK D lam ((p : D.host.K) ^ n * ξ i) - ((y i : ℕ) : ℂ_[p])) -
            (tK D lam (ε : D.host.K) - 1) * ((y i : ℕ) : ℂ_[p]) := by
        simp only [Pi.sub_apply, lyc, map_sub, map_mul, map_inv₀, map_pow, map_natCast]
        field_simp
        ring
      rw [e]
      refine norm_sub_le' (hy i) ?_
      rw [norm_mul]
      have hn1 : ‖((y i : ℕ) : ℂ_[p])‖ ≤ 1 := by simpa using normC_int_le_one (p := p) ((y i : ℕ) : ℤ)
      calc _ ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) * 1 :=
            mul_le_mul he1 hn1 (norm_nonneg _) (pz_pos _).le
        _ ≤ _ := by rw [mul_one]; exact pz_mono (by push_cast; omega)
    · exact (((hξ i).sub ((lyc₂ X.id y i).mono le_rfl (by omega))).mono le_rfl le_rfl).2.trans
        (by simp)
  refine ⟨y, ?_, ?_⟩
  · rw [hqξ, ← cv_sub]
    apply X.h₁.memOf' lam hρ
    rw [cv_sub, ← hqξ]
    exact (PT.trans X.com1 (PT.of_mem hq)).sub (ly_PT X.h₁ ε y)
  · have hPT : PT p La (cv D cc δ b₁ (lyc D p n ε y)) := PT.trans X.com2 (ly_PT X.h₁ ε y)
    rw [cv_change X.hd] at hPT ⊢
    apply X.h.memOf' lam _ hPT
    intro j
    constructor
    · have e : ∑ i, d j i * lyc D p n ε y i = ζ j - ∑ i, d j i * (ξ - lyc D p n ε y) i := by
        rw [← X.dc ζ j, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.sub_apply, hξdef]
        ring
      rw [e]
      have h2 : Bd D lam (∑ i, d j i * (ξ - lyc D p n ε y) i) (0 + 0) (n + 0) :=
        Bd.sum _ fun i _ => (X.bd_d j i).mul (hρ i).bd
      exact (((hζ j).bd.mono le_rfl (show (0 : ℤ) ≤ n + 0 by omega)).sub h2).1.trans (by simp)
    · have h2 : Bd D lam (∑ i, d j i * lyc D p n ε y i) (0 + n) (n + -((n : ℤ) + 2)) :=
        Bd.sum _ fun i _ => (X.bd_d j i).mul (lyc₂ X.id y i)
      exact (h2.mono le_rfl (show (n : ℤ) + -((n : ℤ) + 2) ≤ 0 by omega)).2.trans (by simp)

end Claims

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf.XiMoveP

end Formalism.L2.PairingIndexBounds.Xf.XiMoveP

namespace Formalism.L2.PairingIndexBounds.Xf

end Formalism.L2.PairingIndexBounds.Xf
