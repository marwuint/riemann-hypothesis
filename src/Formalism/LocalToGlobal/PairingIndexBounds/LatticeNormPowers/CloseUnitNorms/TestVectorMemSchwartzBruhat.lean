import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable (D : D7)

theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom

def Lp {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : D.host.E →+* ℂ_[p] :=
  lam.comp (D.host.φ₀.codRestrict (Qbar : IntermediateField ℚ ℂ) (test_vector_mem_schwartz_bruhat D))

theorem lamC_phi_zero_eq (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : D.host.E) :
    lamC lam (D.host.φ₀ x) = Lp D lam x := by
  simp only [lamC, dif_pos (test_vector_mem_schwartz_bruhat D x), Lp]
  rfl

variable {p : ℕ} [hp : Fact p.Prime]

theorem normC_int (k : ℤ) : ‖(k : ℂ_[p])‖ = ‖(k : ℚ_[p])‖ := by
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) k]
  exact PadicComplex.norm_extends' (p := p) _

theorem normC_nat (k : ℕ) : ‖(k : ℂ_[p])‖ = ‖(k : ℚ_[p])‖ := by
  have := normC_int (p := p) (k : ℤ)
  simpa using this

theorem normC_int_le_one (k : ℤ) : ‖(k : ℂ_[p])‖ ≤ 1 := by
  rw [normC_int]; exact Padic.norm_int_le_one k

theorem normC_nat_coprime {s : ℕ} (hs : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [normC_nat]; exact Padic.norm_natCast_eq_one_iff.mpr hs.symm

theorem normC_p_pow (n : ℕ) : ‖(p : ℂ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  rw [← Padic.norm_p_pow, norm_pow, norm_pow, normC_nat]

theorem dvd_of_normC {k : ℤ} {n : ℕ} (h : ‖(k : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    (p ^ n : ℤ) ∣ k := by
  rw [normC_int] at h
  exact (Padic.norm_int_le_pow_iff_dvd k n).mp h

theorem norm_max (x y : ℂ_[p]) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y

section Kstr

variable (D : D7)

abbrev bet : D.host.E := D.host.sqd

theorem bet_sq : bet D * bet D = -(D.host.d : D.host.E) := by
  rw [← sq]; exact Formalism.BasicNotions.Examples₂.bE_sq D.host

theorem d_pos : (0 : ℚ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

theorem K_coords {x : D.host.E} (hx : x ∈ D.host.K) :
    ∃ a b : ℚ, x = (a : D.host.E) + (b : D.host.E) * bet D := by
  have hsq := bet_sq D
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact ⟨0, 1, by simp⟩
  | algebraMap x => exact ⟨x, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - D.host.d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination ((b : D.host.E) * e) * hsq
  | inv x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    have hd := d_pos D
    by_cases h0 : a ^ 2 + D.host.d * b ^ 2 = 0
    · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hd.le (sq_nonneg b)]
      have hb : b = 0 := by
        have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hd.le (sq_nonneg b)]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      subst ha; subst hb
      exact ⟨0, 0, by simp⟩
    · refine ⟨a / (a ^ 2 + D.host.d * b ^ 2), -b / (a ^ 2 + D.host.d * b ^ 2), ?_⟩
      have h0' : ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) ≠ 0 := by exact_mod_cast h0
      apply inv_eq_of_mul_eq_one_right
      rw [Rat.cast_div, Rat.cast_div, Rat.cast_neg]
      field_simp
      push_cast at h0' ⊢
      linear_combination (-(b : D.host.E) ^ 2) * hsq

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.BasicNotions.Examples₂.emb_conj, Formalism.BasicNotions.Examples₂.emb_conj, Complex.conj_conj]

theorem conj_coords (a b : ℚ) :
    D.host.conj ((a : D.host.E) + (b : D.host.E) * bet D) = (a : D.host.E) - (b : D.host.E) * bet D := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, bet, Formalism.BasicNotions.Examples₂.conj_bE]; ring

theorem bet_mem : bet D ∈ D.host.K := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)

theorem conj_mem {x : D.host.E} (hx : x ∈ D.host.K) : D.host.conj x ∈ D.host.K := by
  obtain ⟨a, b, rfl⟩ := K_coords D hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem D.host.K a)
    (mul_mem (SubfieldClass.ratCast_mem D.host.K b) (bet_mem D))

abbrev oE (z : 𝓞 D.host.K) : D.host.E := ((z : D.host.K) : D.host.E)

theorem isInt_oE (z : 𝓞 D.host.K) : IsIntegral ℤ (oE D z) := by
  have h := (RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
  simpa using h

theorem isInt_conj_oE (z : 𝓞 D.host.K) : IsIntegral ℤ (D.host.conj (oE D z)) := by
  have h := (isInt_oE D z).map ((D.host.conj : D.host.E →+* D.host.E).toIntAlgHom)
  simpa using h

theorem int_of_rat {q : ℚ} (h : IsIntegral ℤ (q : D.host.E)) : ∃ k : ℤ, q = k := by
  have h' : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]
    simpa using h
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨k, by simpa using hk.symm⟩

theorem tr_int (z : 𝓞 D.host.K) : ∃ t : ℤ, oE D z + D.host.conj (oE D z) = t := by
  obtain ⟨a, b, hab⟩ := K_coords D (z : D.host.K).2
  change oE D z = _ at hab
  have hs : oE D z + D.host.conj (oE D z) = ((2 * a : ℚ) : D.host.E) := by
    rw [hab, conj_coords]; push_cast; ring
  have hi : IsIntegral ℤ ((2 * a : ℚ) : D.host.E) := hs ▸ (isInt_oE D z).add (isInt_conj_oE D z)
  obtain ⟨k, hk⟩ := int_of_rat D hi
  exact ⟨k, by rw [hs, hk]; push_cast; rfl⟩

theorem nm_int (z : 𝓞 D.host.K) : ∃ n : ℤ, oE D z * D.host.conj (oE D z) = n := by
  obtain ⟨a, b, hab⟩ := K_coords D (z : D.host.K).2
  change oE D z = _ at hab
  have hs : oE D z * D.host.conj (oE D z) = ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) := by
    rw [hab, conj_coords]; push_cast; linear_combination (-(b : D.host.E) ^ 2) * bet_sq D
  have hi : IsIntegral ℤ ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) :=
    hs ▸ (isInt_oE D z).mul (isInt_conj_oE D z)
  obtain ⟨k, hk⟩ := int_of_rat D hi
  exact ⟨k, by rw [hs, hk]; push_cast; rfl⟩

theorem conj_O (z : 𝓞 D.host.K) : ∃ z' : 𝓞 D.host.K, oE D z' = D.host.conj (oE D z) := by
  have hK := conj_mem D (z : D.host.K).2
  set w : D.host.K := ⟨D.host.conj (oE D z), hK⟩
  have hw : IsIntegral ℤ w := by
    rw [← isIntegral_algebraMap_iff (algebraMap D.host.K D.host.E).injective]
    exact isInt_conj_oE D z
  exact ⟨⟨w, hw⟩, rfl⟩

end Kstr

section PadicK

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem Lp_int (k : ℤ) : Lp D lam (k : D.host.E) = (k : ℂ_[p]) := map_intCast _ k

theorem norm_Lp_le_one (z : 𝓞 D.host.K) : ‖Lp D lam (oE D z)‖ ≤ 1 := by
  obtain ⟨t, ht⟩ := tr_int D z
  obtain ⟨n, hn⟩ := nm_int D z
  have hrelE : oE D z ^ 2 = (t : D.host.E) * oE D z - n := by rw [← ht, ← hn]; ring
  have hrel : (Lp D lam (oE D z)) ^ 2 = (t : ℂ_[p]) * Lp D lam (oE D z) - n := by
    have := congrArg (Lp D lam) hrelE
    rwa [map_pow, map_sub, map_mul, Lp_int, Lp_int] at this
  set x := Lp D lam (oE D z)
  by_contra hgt
  push Not at hgt
  have h1 : ‖x‖ ^ 2 ≤ max (‖(t : ℂ_[p])‖ * ‖x‖) ‖(n : ℂ_[p])‖ := by
    rw [← norm_pow, hrel, sub_eq_add_neg]
    calc _ ≤ max ‖(t : ℂ_[p]) * x‖ ‖-(n : ℂ_[p])‖ := norm_max _ _
      _ = _ := by rw [norm_mul, norm_neg]
  have ht1 := normC_int_le_one (p := p) t
  have hn1 := normC_int_le_one (p := p) n
  rcases le_max_iff.mp h1 with h | h
  · nlinarith [norm_nonneg x, norm_nonneg (t : ℂ_[p])]
  · nlinarith

theorem norm_eq_one_of_close {x : ℂ_[p]} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  apply le_antisymm
  · have := norm_max (x - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  · have := norm_max x (1 - x)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at this
    rcases le_max_iff.mp this with h' | h'
    · exact h'
    · linarith

theorem pzpow_le {k m : ℕ} (hkm : k ≤ m) : (p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  apply zpow_le_zpow_right₀
  · exact_mod_cast hp.out.one_lt.le
  · omega

theorem pzpow_lt_one {m : ℕ} (hm : 1 ≤ m) : (p : ℝ) ^ (-(m : ℤ)) < 1 := by
  apply zpow_lt_one_of_neg₀
  · exact_mod_cast hp.out.one_lt
  · omega

theorem lemT (z : 𝓞 D.host.K) {k m : ℕ} (hkm : k ≤ m)
    (h1 : ‖Lp D lam (oE D z)‖ ≤ (p : ℝ) ^ (-(m : ℤ)))
    (h2 : ‖Lp D lam (D.host.conj (oE D z))‖ ≤ (p : ℝ) ^ (-(m : ℤ))) :
    ∃ u : 𝓞 D.host.K, oE D z = (p : D.host.E) ^ k * oE D u := by
  obtain ⟨t, ht⟩ := tr_int D z
  obtain ⟨n, hn⟩ := nm_int D z
  have hpm := pzpow_le (p := p) hkm
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(m : ℤ)) := by positivity
  have htd : ((p ^ k : ℕ) : ℤ) ∣ t := by
    have : ‖(t : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
      rw [← Lp_int D lam, ← ht, map_add]
      exact (norm_max _ _).trans (max_le (h1.trans hpm) (h2.trans hpm))
    have := dvd_of_normC this
    exact_mod_cast this
  have hnd : ((p ^ (2 * k) : ℕ) : ℤ) ∣ n := by
    have : ‖(n : ℂ_[p])‖ ≤ (p : ℝ) ^ (-((2 * k : ℕ) : ℤ)) := by
      rw [← Lp_int D lam, ← hn, map_mul, norm_mul]
      have e : (p : ℝ) ^ (-((2 * k : ℕ) : ℤ)) = (p : ℝ) ^ (-(k : ℤ)) * (p : ℝ) ^ (-(k : ℤ)) := by
        rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; congr 1; push_cast; ring
      rw [e]
      exact mul_le_mul (h1.trans hpm) (h2.trans hpm) (norm_nonneg _) (by positivity)
    have := dvd_of_normC this
    exact_mod_cast this
  obtain ⟨t', rfl⟩ := htd
  obtain ⟨n', rfl⟩ := hnd
  have hp0 : (p : D.host.K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set w : D.host.K := (z : D.host.K) / (p : D.host.K) ^ k with hw
  have hrelE : oE D z ^ 2 - (((p ^ k : ℕ) : ℤ) * t' : ℤ) * oE D z + (((p ^ (2 * k) : ℕ) : ℤ) * n' : ℤ) = 0 := by
    rw [← ht, ← hn]; ring
  have hrelK : w ^ 2 - (t' : D.host.K) * w + (n' : D.host.K) = 0 := by
    have hzw : (z : D.host.K) = (p : D.host.K) ^ k * w := by rw [hw]; field_simp
    have hrelK0 : (z : D.host.K) ^ 2 - (((p ^ k : ℕ) : ℤ) * t' : ℤ) * (z : D.host.K) +
        (((p ^ (2 * k) : ℕ) : ℤ) * n' : ℤ) = 0 := by
      apply (algebraMap D.host.K D.host.E).injective
      simpa using hrelE
    rw [hzw] at hrelK0
    have hpk : ((p : D.host.K) ^ k) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp0)
    apply (mul_right_inj' hpk).mp
    rw [mul_zero, ← hrelK0]
    push_cast; ring
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-t') * Polynomial.X + Polynomial.C n'), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add (Polynomial.degree_linear_lt)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
        Polynomial.eval₂_C]
      rw [← hrelK]; simp; ring
  refine ⟨⟨w, hwi⟩, ?_⟩
  show oE D z = (p : D.host.E) ^ k * ((w : D.host.K) : D.host.E)
  rw [hw]
  have hp0E : (p : D.host.E) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast
  field_simp

end PadicK

section Alg

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem oE_mul (a b : 𝓞 D.host.K) : oE D (a * b) = oE D a * oE D b := by simp [oE]
theorem oE_sub (a b : 𝓞 D.host.K) : oE D (a - b) = oE D a - oE D b := by simp [oE]
theorem oE_one : oE D 1 = 1 := by simp [oE]

theorem norm_one_sub_le {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) : ‖1 - x‖ ≤ 1 := by
  have := norm_max 1 (-x)
  rw [← sub_eq_add_neg, norm_one, norm_neg] at this
  exact this.trans (max_le le_rfl hx)

theorem alg_step (ε : 𝓞 D.host.K) (n : ℕ) (hId : IsIdem D lam (2 * n + 2) ε) (μ : 𝓞 D.host.K) :
    ∃ (c0 : ℤ) (w : 𝓞 D.host.K),
      oE D ε * D.host.conj (oE D μ) = (c0 : D.host.E) * oE D ε + (p : D.host.E) ^ n * oE D w := by
  obtain ⟨h1, h2⟩ := hId
  rw [lamC_phi_zero_eq] at h1 h2
  change ‖Lp D lam (oE D ε) - 1‖ ≤ _ at h1
  change ‖Lp D lam (D.host.conj (oE D ε))‖ ≤ _ at h2
  have hε1 := norm_Lp_le_one D lam ε
  obtain ⟨ε', hε'⟩ := conj_O D ε
  have hε'1 : ‖Lp D lam (D.host.conj (oE D ε))‖ ≤ 1 := hε' ▸ norm_Lp_le_one D lam ε'
  have hkm : n ≤ 2 * n + 2 := by omega
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := by positivity

  obtain ⟨u1, hu1⟩ := lemT D lam (ε * (1 - ε)) hkm (by
      rw [oE_mul, oE_sub, oE_one, map_mul, map_sub, map_one, norm_mul, norm_sub_rev]
      calc _ ≤ 1 * (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := mul_le_mul hε1 h1 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
    (by
      rw [oE_mul, oE_sub, oE_one, map_mul, map_sub, map_one, map_mul, map_sub, map_one, norm_mul]
      calc _ ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) * 1 :=
            mul_le_mul h2 (norm_one_sub_le hε'1) (norm_nonneg _) hpos
        _ = _ := mul_one _)

  obtain ⟨u2, hu2⟩ := lemT D lam (ε * ε') hkm (by
      rw [oE_mul, hε', map_mul, norm_mul]
      calc _ ≤ 1 * (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := mul_le_mul hε1 h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
    (by
      rw [oE_mul, hε', map_mul, conj_conj, map_mul, norm_mul]
      calc _ ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) * 1 := mul_le_mul h2 hε1 (norm_nonneg _) hpos
        _ = _ := mul_one _)
  obtain ⟨μ', hμ'⟩ := conj_O D μ
  obtain ⟨c0, hc0⟩ := tr_int D (ε * μ')
  rw [oE_mul, hμ', map_mul, conj_conj] at hc0
  rw [oE_mul, oE_sub, oE_one] at hu1
  rw [oE_mul, hε'] at hu2
  refine ⟨c0, u1 * μ' - u2 * μ, ?_⟩
  rw [oE_sub, oE_mul, oE_mul, hμ']
  linear_combination (oE D ε) * hc0 + (D.host.conj (oE D μ)) * hu1 - (oE D μ) * hu2

end Alg

section Lat

variable {D : D7} {N N' : ℕ}

theorem Hf_smul_left (T : Tor D) (c : ℂ) (x y : VC D N N') :
    Hf D T (c • x) y = c * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_smul_right (T : Tor D) (c : ℂ) (x y : VC D N N') :
    Hf D T x (c • y) = starRingEnd ℂ c * Hf D T x y := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T (c • y) x, Hf_smul_left, map_mul,
    ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm]

end Lat

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section Tor0

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

variable (D cc δ) in

def ee {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (i : Fin r) : VC D N N' :=
  δ • embV D (tor0 D cc δ) (b i)

end Tor0

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

end Formalism.L2.PairingIndexBounds.Xf.XiOneP
