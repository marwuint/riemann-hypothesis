import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm, ← hs.herm]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]
  ring

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have h1 : ∀ i y, h (b i) y = h' (b i) y := by
    intro i y
    have e := b.ext (f₁ := hs.lin (b i)) (f₂ := hs'.lin (b i)) (fun j => hb i j)
    exact LinearMap.congr_fun e y
  have h3 : ∀ x y, h y x = h' y x := by
    intro x y
    have e := b.ext (f₁ := hs.lin y) (f₂ := hs'.lin y) (fun i => by
      simp only [IsSq.lin_apply]
      rw [hs.herm (b i) y, hs'.herm (b i) y, h1])
    exact LinearMap.congr_fun e x
  exact h3 y x

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by
  exact LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : LinearMap.range (hs.lin e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / h e e) • e, ?_⟩
    rw [IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]
  have e1 := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [hsurj, finrank_top, Module.finrank_self] at e1
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero] at e1
  simp only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1
  rw [Finset.sum_eq_single i] at e1
  · exact (mul_eq_zero.1 e1).resolve_right (h2 i)
  · intro j _ hji
    rw [h1 i j (Ne.symm hji), mul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  have hwe : h w e = 0 := by rw [hs.herm e w, hw, map_zero]
  rw [hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right,
    hs.smul_right, hw, hwe]
  ring

end basic

end PI.VolStabSW.FFHS
