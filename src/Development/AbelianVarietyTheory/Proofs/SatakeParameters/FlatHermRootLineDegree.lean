import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.PullMap

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

theorem prod_prod_erase (g : κ → κ → ℤ) {t : Finset κ} {i : κ} (hi : i ∈ t) (hg : g i i = 1) :
    ∏ a ∈ t, ∏ b ∈ t, g a b =
      (∏ a ∈ t.erase i, ∏ b ∈ t.erase i, g a b) * ∏ a ∈ t.erase i, (g a i * g i a) := by
  have row : ∀ a, ∏ b ∈ t, g a b = g a i * ∏ b ∈ t.erase i, g a b :=
    fun a => (Finset.mul_prod_erase t (g a) hi).symm
  have h1 := Finset.mul_prod_erase t (fun a => ∏ b ∈ t, g a b) hi
  rw [← h1, row i, hg, one_mul, Finset.prod_congr rfl (fun a _ => row a)]
  simp only [Finset.prod_mul_distrib]
  ring

theorem cubeSign_eq_prod (t : Finset κ) (i : κ) :
    cubeSign t i = ∏ a ∈ t, (if a < i then (-1 : ℤ) else 1) := by
  rw [cubeSign, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem cubeSign_image {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) (i : κ) :
    cubeSign (t.image τ) (τ i) = ∏ a ∈ t, (if τ a < τ i then (-1 : ℤ) else 1) := by
  rw [cubeSign_eq_prod, Finset.prod_image (by intro x hx y hy hxy; exact h hx hy hxy)]

theorem pair_sign {τ : κ → ι} {x i : κ} (hx : x ≠ i) (hτ : τ x ≠ τ i) :
    (if x < i ∧ τ i < τ x then (-1 : ℤ) else 1) * (if i < x ∧ τ x < τ i then (-1 : ℤ) else 1) =
      (if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1) := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hτ with h' | h' <;>
    simp [h, h', lt_asymm h, lt_asymm h']

theorem sortSign_eq_erase {τ : κ → ι} {s : Finset κ} {i : κ} (hi : i ∈ s)
    (hne : ∀ x ∈ s.erase i, τ x ≠ τ i) :
    sortSign τ s = sortSign τ (s.erase i) *
      ∏ x ∈ s.erase i, ((if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1)) := by
  have := prod_prod_erase (fun x y => if x < y ∧ τ y < τ x then (-1 : ℤ) else 1) hi (by simp)
  beta_reduce at this
  unfold sortSign
  rw [this]
  congr 1
  exact Finset.prod_congr rfl fun x hx => pair_sign (Finset.ne_of_mem_erase hx) (hne x hx)

theorem sign_inj {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    sortSign τ t * cubeSign (t.image τ) (τ i) = cubeSign t i * sortSign τ (t.erase i) := by
  have e1 := sortSign_eq_erase (τ := τ) hi (fun x hx e =>
    Finset.ne_of_mem_erase hx (h (Finset.mem_of_mem_erase hx) hi e))
  rw [Finset.prod_mul_distrib] at e1
  have e2 : cubeSign t i = ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hi]
    simp
  have e3 : cubeSign (t.image τ) (τ i) = ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) := by
    rw [cubeSign_image h, ← Finset.mul_prod_erase t _ hi]
    simp
  have hQ : (∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1)) *
      ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => by split_ifs <;> norm_num
  rw [e1, e2, e3]
  linear_combination (sortSign τ (t.erase i) * ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1)) * hQ

theorem sign_pair {τ : κ → ι} {t : Finset κ} {a b : κ} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) :
    cubeSign t a * sortSign τ (t.erase a) = -(cubeSign t b * sortSign τ (t.erase b)) := by
  have hb' : b ∈ t.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have ha' : a ∈ t.erase b := Finset.mem_erase.2 ⟨hab, ha⟩
  have hu' : (t.erase b).erase a = (t.erase a).erase b := Finset.erase_right_comm
  have mem : ∀ x ∈ (t.erase a).erase b, τ x ≠ τ b := by
    intro x hx e
    have hx1 := Finset.mem_erase.1 hx
    exact hx1.1 (h hx1.2 hb' e)
  have e1 := sortSign_eq_erase (τ := τ) hb' mem
  have e2 := sortSign_eq_erase (τ := τ) ha' (by rw [hu', he]; exact mem)
  rw [hu', he] at e2
  have c1 : cubeSign t a = (if b < a then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < a then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hb, ← Finset.mul_prod_erase (t.erase b) _ ha', hu']
    simp only [lt_self_iff_false, if_false, one_mul]
  have c2 : cubeSign t b = (if a < b then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < b then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ ha, ← Finset.mul_prod_erase (t.erase a) _ hb']
    simp only [lt_self_iff_false, if_false, one_mul]
  have hs : (if b < a then (-1 : ℤ) else 1) = -(if a < b then (-1 : ℤ) else 1) := by
    rcases lt_or_gt_of_ne hab with h' | h' <;> simp [h', lt_asymm h']
  rw [e1, e2, c1, c2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs]
  ring

theorem image_erase_of_injOn {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    (t.image τ).erase (τ i) = (t.erase i).image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun e => hy (congrArg τ e), hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxi, hx⟩, rfl⟩
    exact ⟨fun e => hxi (h hx hi e), x, hx, rfl⟩

theorem image_erase_eq {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b) (he : τ a = τ b) :
    (t.erase a).image τ = t.image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hxa]; exact he.symm⟩
    · exact ⟨x, ⟨hxa, hx⟩, rfl⟩

theorem injOn_erase_swap {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) : Set.InjOn τ (t.erase b) := by
  intro x hx y hy hxy
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
  have hb' : b ∈ (↑(t.erase a) : Set κ) := by simp [hab.symm, hb]
  by_cases hxa : x = a <;> by_cases hya : y = a
  · rw [hxa, hya]
  · exact absurd (h (by simp [hya, hy.1]) hb' (by rw [← hxy, hxa, he])) hy.2
  · exact absurd (h (by simp [hxa, hx.1]) hb' (by rw [hxy, hya, he])) hx.2
  · exact h (by simp [hxa, hx.1]) (by simp [hya, hy.1]) hxy

variable {k : Type} [Field k] {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

open Classical in

theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

end GlobalTheory.PD.PullMap

namespace GlobalTheory.PD

end GlobalTheory.PD
