import Mathlib

noncomputable section

namespace PositivityTheory.ThKF.Abs

open scoped InnerProductSpace

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem orth_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (z : U) (hz : z ∈ Yᗮ) : κ k z ∈ Yᗮ := by
  rw [Submodule.mem_orthogonal] at hz ⊢
  intro y hy
  have e : y = κ k (κ k⁻¹ y) := by rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [e, hi]
  exact hz _ (hY _ _ hy)

theorem span_orbit_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) (k : K) :
    ∀ y ∈ Submodule.span ℂ (Set.range fun k => κ k x), κ k y ∈ Submodule.span ℂ (Set.range fun k => κ k x) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => obtain ⟨k', rfl⟩ := h; exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

def orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : Submodule ℂ U := Submodule.span ℂ (Set.range fun k => κ k x)

theorem mem_orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : x ∈ orb κ x := Submodule.subset_span ⟨1, by simp⟩

def Proj (St : Submodule ℂ U → Prop) : Prop :=
  ∀ f : U, ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
    ∀ S : Submodule ℂ U, St S → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z

theorem compl {St : Submodule ℂ U → Prop} (h : Proj St) (S : Submodule ℂ U) (hS : St S) (f : U) :
    ∃ a ∈ S, f - a ∈ Sᗮ := by
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  let A : Submodule ℂ U := S ⊓ Z
  haveI : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
  have ha := A.starProjection_apply_mem f
  refine ⟨_, ha.1, fun u hu => ?_⟩
  obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd S hS u hu
  have h1 : f - A.starProjection f ∈ Z'ᗮ := e ▸ sub_mem hf ha.2
  rw [inner_add_left, A.sub_starProjection_mem_orthogonal f y ⟨hy, hyZ⟩, h1 z hz, add_zero]

end PositivityTheory.ThKF.Abs

end
