import Mathlib

open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)

def orbitSum (K : Subgroup G) (v : E) (hv : (Set.range fun k : K => ρ k v).Finite) : E :=
  ∑ w ∈ hv.toFinset, w

variable {ρ}

theorem orbitSum_mem {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  obtain ⟨k, rfl⟩ := hw
  exact hY _ _ hvY

end

variable {ρ : Representation ℂ G E} {ι : E →ₗ[ℂ] H} {T : Submodule ℂ E} {φ : E}

end GL2Classical

end

end GroundTheory.Automorphic
