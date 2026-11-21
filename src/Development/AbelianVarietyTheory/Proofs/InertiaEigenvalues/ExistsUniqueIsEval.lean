import Mathlib

namespace GlobalTheory.DiscEval

open PowerSeries Finset

variable (p : ℕ) {A K C B C' B' : Type*} [CommRing A] [CommRing K] [CommRing C] [CommRing B] [CommRing C']
  [CommRing B']

def Tends (i : C →+* B) (s : ℕ → B) (y : B) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ z : C, s n - y = i ((p : C) ^ r * z)

def OnDisc (a : A →+* K) (L : PowerSeries K) : Prop :=
  ∀ M : ℕ, 0 < M → ∃ D : ℕ, ∀ k : ℕ, ∃ b : A, (p : K) ^ (D + k / M) * coeff k L = a b

noncomputable def psum (κ : K →+* B) (L : PowerSeries K) (x : B) (n : ℕ) : B :=
  ∑ k ∈ range n, κ (coeff k L) * x ^ k

def IsEval (i : C →+* B) (κ : K →+* B) (L : PowerSeries K) (x y : B) : Prop := Tends p i (psum κ L x) y

variable {p} {i : C →+* B} {i' : C' →+* B'} {κ : K →+* B} {a : A →+* K} {o : A →+* C}

theorem eq_zero_of_dvd [h : IsHausdorff (Ideal.span {(p : C)}) C] {z : C} (hz : ∀ r : ℕ, (p : C) ^ r ∣ z) :
    z = 0 :=
  h.haus' z fun r => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hz r

theorem Tends.unique [IsHausdorff (Ideal.span {(p : C)}) C] (hi : Function.Injective i) {s : ℕ → B} {y y' : B}
    (h : Tends p i s y) (h' : Tends p i s y') : y = y' := by
  have key : ∀ r : ℕ, ∃ z : C, y - y' = i ((p : C) ^ r * z) := fun r => by
    obtain ⟨N, hN⟩ := h r
    obtain ⟨N', hN'⟩ := h' r
    obtain ⟨z, hz⟩ := hN (max N N') (le_max_left _ _)
    obtain ⟨z', hz'⟩ := hN' (max N N') (le_max_right _ _)
    exact ⟨z' - z, by rw [mul_sub, map_sub, ← hz, ← hz']; ring⟩
  obtain ⟨z, hz⟩ := key 0
  rw [pow_zero, one_mul] at hz
  have : z = 0 := eq_zero_of_dvd (p := p) fun r => (key r).imp fun w hw => hi (hz.symm.trans hw)
  rwa [this, map_zero, sub_eq_zero] at hz

theorem Tends.map (ψ : B →+* B') (hψ : ∀ z, ∃ z', ψ (i z) = i' z') {s : ℕ → B} {y : B}
    (h : Tends p i s y) : Tends p i' (fun n => ψ (s n)) (ψ y) := fun r =>
  (h r).imp fun N hN n hn => by
    obtain ⟨z, hz⟩ := hN n hn
    obtain ⟨z', hz'⟩ := hψ z
    exact ⟨z', by simp only [← map_sub, hz, map_mul, map_pow, map_natCast, hz']⟩

theorem Tends.add {s t : ℕ → B} {y w : B} (h : Tends p i s y) (h' : Tends p i t w) :
    Tends p i (fun n => s n + t n) (y + w) := fun r => by
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  refine ⟨max N N', fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n (le_of_max_le_left hn)
  obtain ⟨z', hz'⟩ := hN' n (le_of_max_le_right hn)
  exact ⟨z + z', by rw [mul_add, map_add, ← hz, ← hz']; ring⟩

theorem pow_div_dvd {x : C} {M : ℕ} (hx : (p : C) ∣ x ^ M) (k : ℕ) : (p : C) ^ (k / M) ∣ x ^ k := by
  refine (pow_dvd_pow_of_dvd hx _).trans ?_
  rw [← pow_mul]
  exact pow_dvd_pow _ (Nat.mul_div_le k M)

theorem two_mul_div_le (k M : ℕ) : k / (M * 2) + k / (M * 2) ≤ k / M := by
  rw [← Nat.div_div_eq_div_mul]
  omega

theorem term_bound (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} {M D : ℕ}
    (hD : ∀ k : ℕ, ∃ b : A, (p : K) ^ (D + k / (M * 2)) * coeff k L = a b) {k n : ℕ} (hk : k ≤ n) {z : C}
    (hz : (p : C) ^ (n / M) ∣ z) :
    ∃ w : C, (p : B) ^ D * (κ (coeff k L) * i z) = i ((p : C) ^ (n / (M * 2)) * w) := by
  obtain ⟨b, hb⟩ := hD k
  obtain ⟨w, rfl⟩ := hz
  have h1 : k / (M * 2) + n / (M * 2) ≤ n / M :=
    (Nat.add_le_add_right (Nat.div_le_div_right hk) _).trans (two_mul_div_le n M)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  have h2 := congrArg κ hb
  refine ⟨(p : C) ^ d * o b * w, ?_⟩
  simp only [map_mul, map_pow, map_natCast, h, hd, ← h2]
  ring

theorem IsEval.map {K' : Type*} [CommRing K'] {κ' : K' →+* B'} (ψ : B →+* B') (τ : K →+* K')
    (hψ : ∀ z, ∃ z', ψ (i z) = i' z') (hκ : ∀ c, ψ (κ c) = κ' (τ c)) {L : PowerSeries K} {x y : B}
    (h : IsEval p i κ L x y) : IsEval p i' κ' (PowerSeries.map τ L) (ψ x) (ψ y) := by
  have := Tends.map ψ hψ h
  intro r
  simpa only [psum, map_sum, map_mul, map_pow, hκ, coeff_map] using this r

theorem pow_sub_dvd (u : PowerSeries A) {x y d : C} {n : ℕ} (hx : d ∣ x ^ n)
    (hy : d ∣ y - ∑ j ∈ range n, o (coeff j u) * x ^ j) (k : ℕ) :
    d ∣ y ^ k - ∑ j ∈ range n, o (coeff j (u ^ k)) * x ^ j := by
  have e : ∀ v : PowerSeries A, ∑ j ∈ range n, o (coeff j v) * x ^ j = Polynomial.eval₂RingHom o x (trunc n v) :=
    fun v => (eval₂_trunc_eq_sum_range x o n v).symm
  rw [e] at hy ⊢
  have h1 : Polynomial.X ^ n ∣ trunc n u ^ k - trunc n (u ^ k) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro j hj
    rw [Polynomial.coeff_sub, ← trunc_trunc_pow, coeff_trunc, if_pos hj, ← Polynomial.coe_pow,
      Polynomial.coeff_coe, sub_self]
  have h2 := map_dvd (Polynomial.eval₂RingHom o x) h1
  rw [map_pow, map_sub, map_pow, show Polynomial.eval₂RingHom o x Polynomial.X = x from
    Polynomial.eval₂_X o x] at h2
  have := dvd_add (hy.trans (sub_dvd_pow_sub_pow _ _ k)) (hx.trans h2)
  rwa [sub_add_sub_cancel] at this

theorem coeff_pow_of_lt {u : PowerSeries K} (hu : constantCoeff u = 0) {m k : ℕ} (h : k < m) :
    coeff k (u ^ m) = 0 := by
  obtain ⟨v, rfl⟩ := X_dvd_iff.2 hu
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem IsEval.subst (hp : IsUnit (p : B)) (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L)
    {u : PowerSeries A} (hu : constantCoeff u = 0) {x y : C} {M : ℕ} (hM : 0 < M) (hx : (p : C) ∣ x ^ M)
    (hy : ∀ n, (p : C) ^ (n / M) ∣ y - ∑ j ∈ range n, o (coeff j u) * x ^ j) {w : B}
    (hw : IsEval p i κ L (i y) w) : IsEval p i κ (L.subst (PowerSeries.map a u)) (i x) w := by
  have hN : 0 < M * 2 := by omega
  obtain ⟨D, hD⟩ := hL (M * 2) hN
  have hu' : constantCoeff (PowerSeries.map a u) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have hc : ∀ n j, j < n → coeff j (L.subst (PowerSeries.map a u)) =
      ∑ k ∈ range n, coeff k L * a (coeff j (u ^ k)) := fun n j hj => by
    rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hu'), finsum_eq_sum_of_support_subset (s := range n)]
    · simp only [smul_eq_mul, ← map_pow, coeff_map]
    · intro m hm
      rw [Function.mem_support] at hm
      by_contra hc
      simp only [coe_range, Set.mem_Iio, not_lt] at hc
      exact hm (by rw [coeff_pow_of_lt hu' (by omega), smul_zero])
  have hs : ∀ n, psum κ L (i y) n - psum κ (L.subst (PowerSeries.map a u)) (i x) n =
      ∑ k ∈ range n, κ (coeff k L) * i (y ^ k - ∑ j ∈ range n, o (coeff j (u ^ k)) * x ^ j) := fun n => by
    have e : psum κ (L.subst (PowerSeries.map a u)) (i x) n =
        ∑ j ∈ range n, ∑ k ∈ range n, κ (coeff k L * a (coeff j (u ^ k))) * i x ^ j :=
      sum_congr rfl fun j hj => by rw [hc n j (mem_range.1 hj), map_sum, sum_mul]
    rw [e, psum, sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [map_sub, map_sum, map_mul, map_pow i, h, mul_sub, mul_sum, mul_assoc]
  intro r
  obtain ⟨N, hN'⟩ := hw r
  refine ⟨max N ((D + r) * (M * 2)), fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN' n (le_of_max_le_left hn)
  choose! v hv using fun k (hk : k ∈ range n) =>
    term_bound h hD (mem_range.1 hk).le (pow_sub_dvd u (pow_div_dvd hx n) (hy n) k)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ((Nat.le_div_iff_mul_le hN).2 (le_of_max_le_right hn))
  have h2 : psum κ L (i y) n - psum κ (L.subst (PowerSeries.map a u)) (i x) n =
      i ((p : C) ^ r * ((p : C) ^ d * ∑ k ∈ range n, v k)) := by
    refine (hp.pow D).mul_left_cancel ?_
    rw [hs, mul_sum, sum_congr rfl hv, ← map_sum, ← mul_sum]
    simp only [hd, map_mul, map_pow, map_natCast]
    ring
  exact ⟨z - (p : C) ^ d * ∑ k ∈ range n, v k, by rw [mul_sub, map_sub, ← hz, ← h2]; ring⟩

end GlobalTheory.DiscEval
