import Mathlib

noncomputable section

namespace PI.VolStabW.FFHS

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
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm z x, ← hs.herm z y]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z :=
  (hs.lin x).map_sub y z

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y

end basic

end PI.VolStabW.FFHS
