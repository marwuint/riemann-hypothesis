import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLSpace
import GroundTheory.AutomorphicForms.WhittakerCriterion

noncomputable section

open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.PfBern.Loc

abbrev SC (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) :=
  locallyConstantCompactSupport X ℂ ℂ

abbrev Distr (X : Type*) [TopologicalSpace X] : Type _ := Module.Dual ℂ (SC X)

variable {X : Type*} [TopologicalSpace X]

def mulInd (A : Set X) (hA : IsClopen A) : SC X →ₗ[ℂ] SC X where
  toFun f := ⟨fun x => A.indicator 1 x * (f : X → ℂ) x,
    (indicator_mul_mem (U := univ) hA ⟨f.2, subset_univ _⟩).1⟩
  map_add' f g := Subtype.ext <| funext fun x => by simp [mul_add]
  map_smul' c f := Subtype.ext <| funext fun x => by simp [mul_left_comm]

@[simp]
theorem coe_mulInd (A : Set X) (hA : IsClopen A) (f : SC X) :
    ((mulInd A hA f : SC X) : X → ℂ) = fun x => A.indicator 1 x * (f : X → ℂ) x :=
  rfl

section Restrict

variable {Z : Set X}

def restr (hZ : IsClosed Z) : SC X →ₗ[ℂ] SC Z where
  toFun f := ⟨fun z => (f : X → ℂ) z,
    ⟨f.2.1.comp_continuous continuous_subtype_val,
      f.2.2.comp_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_restr (hZ : IsClosed Z) (f : SC X) :
    ((restr hZ f : SC Z) : Z → ℂ) = fun z : Z => (f : X → ℂ) z :=
  rfl

def extendDistr (hZ : IsClosed Z) (D' : Distr Z) : Distr X :=
  D'.comp (restr hZ)

theorem extendDistr_apply (hZ : IsClosed Z) (D' : Distr Z) (f : SC X) :
    extendDistr hZ D' f = D' (restr hZ f) :=
  rfl

theorem restr_compHomeoL (hZ : IsClosed Z) (e : X ≃ₜ X) (heZ : ∀ x, x ∈ Z ↔ e x ∈ Z)
    (f : SC X) :
    restr hZ (compHomeoL e f) = compHomeoL (e.subtype heZ) (restr hZ f) :=
  rfl

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem restr_surjective (hZ : IsClosed Z) : Function.Surjective (restr hZ) := by
  intro φ
  obtain ⟨f, hf, hfφ⟩ := exists_lift (U := univ) isOpen_univ (subset_univ Z) φ.2
  exact ⟨⟨f, hf.1⟩, Subtype.ext (funext hfφ)⟩

end Restrict

section Transport

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

def pullL (h : A ≃ₜ B) : SC B →ₗ[ℂ] SC A where
  toFun f := ⟨fun a => (f : B → ℂ) (h a), f.2.1.comp_continuous h.continuous, f.2.2.comp_homeomorph h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullL_pullL_symm (h : A ≃ₜ B) (f : SC A) : pullL h (pullL h.symm f) = f :=
  Subtype.ext <| funext fun a => by simp [pullL]

end Transport

end PositivityTheory.PfBern.Loc

end
