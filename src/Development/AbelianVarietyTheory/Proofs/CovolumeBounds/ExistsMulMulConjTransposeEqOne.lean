import Mathlib

open Module

namespace GlobalTheory.FiniteOrders

section Field

variable {K : Type*} [Field K] [StarRing K]

theorem exists_mul_star_eq_of_norm_eq_one (hs : ∃ a : K, star a ≠ a) {u : K}
    (hu : u * star u = 1) : ∃ z : K, z ≠ 0 ∧ u * star z = z := by
  have key : ∃ a : K, a + u * star a ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨a, ha⟩ := hs
    have h1 := hne 1
    have h2 := hne a
    rw [star_one] at h1
    exact ha (by linear_combination (star a) * h1 - h2)
  obtain ⟨a, ha⟩ := key
  refine ⟨_, ha, ?_⟩
  rw [star_add, star_mul', star_star]
  linear_combination a * hu

private def normHom (K : Type*) [Field K] [StarRing K] : Kˣ →* Kˣ :=
  MonoidHom.mk' (fun z => z * star z) (by
    intro a b; rw [star_mul']; exact mul_mul_mul_comm _ _ _ _)

private def quotHom (K : Type*) [Field K] [StarRing K] : Kˣ →* Kˣ :=
  MonoidHom.mk' (fun z => z / star z) (by
    intro a b; rw [star_mul']; exact mul_div_mul_comm _ _ _ _)

private theorem mem_ker_normHom (z : Kˣ) : z ∈ (normHom K).ker ↔ (z : K) * star (z : K) = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]; simp [normHom]

private theorem mem_ker_quotHom (z : Kˣ) : z ∈ (quotHom K).ker ↔ star (z : K) = z := by
  rw [MonoidHom.mem_ker]
  change z / star z = 1 ↔ _
  rw [div_eq_one, Units.ext_iff, Units.coe_star, eq_comm]

private theorem range_quotHom (hs : ∃ a : K, star a ≠ a) :
    (quotHom K).range = (normHom K).ker := by
  ext u
  rw [mem_ker_normHom]
  constructor
  · rintro ⟨z, rfl⟩
    have h1 : (z : K) ≠ 0 := z.ne_zero
    have h2 : star (z : K) ≠ 0 := star_ne_zero.2 h1
    simp only [quotHom, MonoidHom.mk'_apply, Units.val_div_eq_div_val, Units.coe_star, star_div₀,
      star_star]
    field_simp
  · intro hu
    obtain ⟨z, hz, h⟩ := exists_mul_star_eq_of_norm_eq_one hs hu
    refine ⟨Units.mk0 z hz, Units.ext ?_⟩
    have h2 : star z ≠ 0 := star_ne_zero.2 hz
    simp only [quotHom, MonoidHom.mk'_apply, Units.val_div_eq_div_val, Units.coe_star,
      Units.val_mk0]
    rw [div_eq_iff h2, h]

private theorem card_ker_mul_card_range {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

private theorem range_normHom [Finite K] (hs : ∃ a : K, star a ≠ a) :
    (normHom K).range = (quotHom K).ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨z, rfl⟩
    rw [mem_ker_quotHom]
    simp [normHom, mul_comm]
  · have h1 := card_ker_mul_card_range (normHom K)
    have h2 := card_ker_mul_card_range (quotHom K)
    rw [range_quotHom hs, ← h1, mul_comm] at h2
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).le

theorem exists_mul_star_eq [Finite K] (hs : ∃ a : K, star a ≠ a) {c : K} (hc : star c = c) :
    ∃ t : K, t * star t = c := by
  by_cases h0 : c = 0
  · exact ⟨0, by simp [h0]⟩
  have : Units.mk0 c h0 ∈ (normHom K).range := by
    rw [range_normHom hs, mem_ker_quotHom]; exact hc
  obtain ⟨t, ht⟩ := this
  exact ⟨t, by simpa [normHom] using congrArg Units.val ht⟩

end Field

section Sphere

variable {K : Type*} [Field K] [StarRing K]

end Sphere

section Frames

variable {K : Type*} [Field K] [StarRing K]

def IsOrthonormal {V : Type*} [AddCommGroup V] [Module K V] (h : V →ₗ[K] V →ₗ⋆[K] K)
    {ι : Type*} [DecidableEq ι] (s : ι → V) : Prop :=
  ∀ i j, h (s i) (s j) = if i = j then 1 else 0

section

variable {V : Type*} [AddCommGroup V] [Module K V] {h : V →ₗ[K] V →ₗ⋆[K] K}

theorem IsOrthonormal.linearIndependent {ι : Type*} [DecidableEq ι] {s : ι → V}
    (hs : IsOrthonormal h s) : LinearIndependent K s := by
  rw [linearIndependent_iff']
  intro t g hg i hi
  have := congrArg (fun v => h v (s i)) hg
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hs _ i, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hi, if_true, map_zero,
    LinearMap.zero_apply] at this
  exact this

theorem IsOrthonormal.apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι K V}
    (hb : IsOrthonormal h b) (x y : V) : h x y = ∑ i, b.repr x i * star (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    hb _ _, smul_eq_mul, mul_ite, mul_one, mul_zero, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem exists_apply_self_eq_one [Finite K] (hs : ∃ a : K, star a ≠ a)
    (hh : ∀ x y, h y x = star (h x y)) {x y : V} (hxy : h x y ≠ 0) : ∃ v, h v v = 1 := by
  have key : ∃ v, h v v ≠ 0 := by
    by_contra hne
    push Not at hne
    have htr : ∀ b : K, b + star b = 0 := by
      intro b
      have h1 := hne ((b / h x y) • x + y)
      simp only [map_add, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply,
        LinearMap.smul_apply, hne, smul_eq_mul, starRingEnd_apply, hh x y, mul_zero, zero_add,
        add_zero, ← star_mul', div_mul_cancel₀ _ hxy] at h1
      linear_combination h1
    obtain ⟨a, ha⟩ := hs
    have h1 := htr 1
    rw [star_one] at h1
    exact ha (by linear_combination htr a - a * h1)
  obtain ⟨v, hv⟩ := key
  obtain ⟨t, ht⟩ := exists_mul_star_eq hs (c := (h v v)⁻¹) (by rw [star_inv₀, ← hh])
  refine ⟨t • v, ?_⟩
  simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have := mul_inv_cancel₀ hv
  linear_combination (h v v) * ht + this

private abbrev perp (h : V →ₗ[K] V →ₗ⋆[K] K) (v : V) : Submodule K V := LinearMap.ker (h.flip v)

private abbrev res (h : V →ₗ[K] V →ₗ⋆[K] K) (v : V) : perp h v →ₗ[K] perp h v →ₗ⋆[K] K :=
  h.domRestrict₁₂ (perp h v) (perp h v)

@[simp] private theorem res_apply (v : V) (x y : perp h v) : res h v x y = h x y := rfl

private theorem finrank_perp [FiniteDimensional K V] {v : V} (hv : h v v = 1) {n : ℕ}
    (hn : finrank K V = n + 1) : finrank K (perp h v) = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
  have h2 : LinearMap.range (h.flip v) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • v, by simp [hv]⟩
  rw [h2, finrank_top, finrank_self, hn] at h1
  change finrank K (LinearMap.ker (h.flip v)) = n
  omega

private theorem res_nondeg (hh : ∀ x y, h y x = star (h x y))
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {v : V} (hv : h v v = 1) (x : perp h v)
    (hx : ∀ y, res h v x y = 0) : x = 0 := by
  apply Subtype.ext
  apply hnd
  intro y
  have h1 := hx ⟨y - h y v • v, by simp [hv]⟩
  have h2 : h x v = 0 := x.2
  simpa [LinearMap.map_smulₛₗ, h2] using h1

private theorem isOrthonormal_cons (hh : ∀ x y, h y x = star (h x y)) {v : V} (hv : h v v = 1)
    {n : ℕ} {s : Fin n → perp h v} (hs : IsOrthonormal (res h v) s) :
    IsOrthonormal h (Fin.cons v fun i => (s i : V) : Fin (n + 1) → V) := by
  have h0 : ∀ i, h (s i) v = 0 := fun i => (s i).2
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [hv]
  · simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hh, h0, star_zero, if_neg (Fin.succ_ne_zero j).symm]
  · simp [h0]
  · simpa using hs i j

end

universe u

private theorem exists_frame [Finite K] (hs : ∃ a : K, star a ≠ a) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V →ₗ[K] V →ₗ⋆[K] K), (∀ x y, h y x = star (h x y)) →
      (∀ x, (∀ y, h x y = 0) → x = 0) → finrank K V = n →
      ∃ s : Fin n → V, IsOrthonormal h s := by
  induction n with
  | zero => intro V _ _ _ h _ _ _; exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hh hnd hn
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hx (hnd x hne)
    obtain ⟨v, hv⟩ := exists_apply_self_eq_one hs hh hy
    obtain ⟨s, hs⟩ := ih (perp h v) (res h v) (fun x y => hh x y) (res_nondeg hh hnd hv)
      (finrank_perp hv hn)
    exact ⟨_, isOrthonormal_cons hh hv hs⟩

theorem exists_orthonormal_basis [Finite K] (hs : ∃ a : K, star a ≠ a)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ[K] V →ₗ⋆[K] K} (hh : ∀ x y, h y x = star (h x y))
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = finrank K V) : ∃ b : Basis ι K V, IsOrthonormal h b := by
  obtain ⟨s, hs⟩ := exists_frame hs _ V h hh hnd rfl
  let e : ι ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq hι
  have hs' : IsOrthonormal h (s ∘ e) := fun i j => by
    simpa using hs (e i) (e j)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hs'.linearIndependent hι, ?_⟩
  simpa using hs'

end Frames

section Groups

variable {K : Type*} [Field K] [StarRing K]

private def gramForm {ι : Type*} [Fintype ι] (H : Matrix ι ι K) :
    (ι → K) →ₗ[K] (ι → K) →ₗ⋆[K] K :=
  LinearMap.mk₂'ₛₗ (RingHom.id K) (starRingEnd K) (fun x y => x ⬝ᵥ H.mulVec (star y))
    (fun x x' y => add_dotProduct _ _ _)
    (fun c x y => by simp [smul_dotProduct])
    (fun x y y' => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul, starRingEnd_apply])

private theorem prod_eq (q ε : ℚ) (hq : q ≠ 0) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), q ^ i * (q ^ (i + 1) - ε ^ (i + 1)) =
      (q ^ ((n + 1) ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 (n + 1), (1 - ε ^ i * (q ^ i)⁻¹)) * (q - ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1 + 1)]
    have : (n + 1 + 1) ^ 2 - 1 = ((n + 1) ^ 2 - 1) + (n + 1) + (n + 1 + 1) := by
      have h1 : (n + 1 + 1) ^ 2 = (n + 1) ^ 2 + (n + 1) + (n + 1 + 1) := by ring
      have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [this, pow_add q (_ + (n + 1)) (n + 1 + 1), pow_add q (_ - 1) (n + 1)]
    field_simp

end Groups

section Linear

variable {F : Type*} [Field F] [Finite F]

end Linear

end GlobalTheory.FiniteOrders
