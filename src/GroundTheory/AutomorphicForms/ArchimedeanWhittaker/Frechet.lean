import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ContinuousMultilinearOfFiniteDimensional

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

noncomputable def wordSeminorm (Y : Σ k, Fin k → 𝔤) : Seminorm ℂ (h.smoothVectors π) :=
  Seminorm.of (fun v => ‖h.wordOp π Y.2 (v : E)‖)
    (fun v w => by
      simp only [Submodule.coe_add]
      rw [h.wordOp_add π v.2 w.2]
      exact norm_add_le _ _)
    (fun c v => by
      simp only [Submodule.coe_smul]
      rw [h.wordOp_smul π v.2, norm_smul])

def SmoothFrechet : Type _ := h.smoothVectors π

noncomputable instance : AddCommGroup (h.SmoothFrechet π) :=
  inferInstanceAs (AddCommGroup (h.smoothVectors π))

noncomputable instance : Module ℂ (h.SmoothFrechet π) :=
  inferInstanceAs (Module ℂ (h.smoothVectors π))

noncomputable def smoothSeminormFamily : SeminormFamily ℂ (h.SmoothFrechet π) (Σ k, Fin k → 𝔤) :=
  fun Y => h.wordSeminorm π Y

noncomputable instance : TopologicalSpace (h.SmoothFrechet π) :=
  (h.smoothSeminormFamily π).moduleFilterBasis.topology

theorem withSeminorms_smoothFrechet : WithSeminorms (h.smoothSeminormFamily π) := ⟨rfl⟩

instance : IsTopologicalAddGroup (h.SmoothFrechet π) :=
  (h.withSeminorms_smoothFrechet π).topologicalAddGroup

instance : ContinuousSMul ℂ (h.SmoothFrechet π) :=
  (h.withSeminorms_smoothFrechet π).continuousSMul

def IsSmoothContinuous (l : h.smoothVectors π →ₗ[ℂ] ℂ) : Prop :=
  ∃ (s : Finset (Σ k, Fin k → 𝔤)) (C : ℝ), ∀ v, ‖l v‖ ≤ C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (v : E)‖

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

variable {h π}

variable (h π) in

def smoothMap {v : E} (hv : h.IsSmoothVector π v) (g : G) : h.smoothVectors π :=
  ⟨π g v, h.isSmoothVector_map π hv g⟩

@[simp] theorem coe_smoothMap {v : E} (hv : h.IsSmoothVector π v) (g : G) :
    (h.smoothMap π hv g : E) = π g v := rfl

end IsExpLieAlgebra

end GroundTheory.Automorphic
