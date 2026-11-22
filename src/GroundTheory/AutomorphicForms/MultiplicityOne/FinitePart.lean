import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteFactor
import GroundTheory.AutomorphicForms.SmoothRep

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep (normOneGL K n) H)

abbrev archRep : UnitaryRep (ArchUnits K n) H := σ.compHom (archProj K n) continuous_archProj

variable (V₀ : Submodule ℂ H) [CompleteSpace V₀] (hV₀ : (archRep σ).IsInvariant V₀)

def archType : UnitaryRep (ArchUnits K n) V₀ := (archRep σ).restrict V₀ hV₀

def homArch : Submodule ℂ (V₀ →L[ℂ] H) := (archType σ V₀ hV₀).intertwiners (archRep σ)

theorem finProj_comp_mem_homArch (w : AdelicGLn.FiniteAdelicGL K n) {S : V₀ →L[ℂ] H}
    (hS : S ∈ homArch σ V₀ hV₀) : σ (finProj K n w) ∘L S ∈ homArch σ V₀ hV₀ := by
  intro A v
  show σ (finProj K n w) (S (archType σ V₀ hV₀ A v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [hS A v]
  show σ (finProj K n w) (σ (archProj K n A) (S v)) = σ (archProj K n A) (σ (finProj K n w) (S v))
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, finProj_mul_archProj_comm]

def HomSpace : Type _ := homArch σ V₀ hV₀

instance : AddCommGroup (HomSpace σ V₀ hV₀) := inferInstanceAs (AddCommGroup (homArch σ V₀ hV₀))

instance : Module ℂ (HomSpace σ V₀ hV₀) := inferInstanceAs (Module ℂ (homArch σ V₀ hV₀))

def HomSpace.op (S : HomSpace σ V₀ hV₀) : V₀ →L[ℂ] H := (S : homArch σ V₀ hV₀).1

def finRep : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (HomSpace σ V₀ hV₀) where
  toFun w :=
    { toFun := fun S => (⟨σ (finProj K n w) ∘L (S : homArch σ V₀ hV₀).1,
        finProj_comp_mem_homArch σ V₀ hV₀ w (S : homArch σ V₀ hV₀).2⟩ : homArch σ V₀ hV₀)
      map_add' := fun S S' => Subtype.ext (ContinuousLinearMap.comp_add _ _ _)
      map_smul' := fun c S => Subtype.ext (ContinuousLinearMap.comp_smul _ _ _) }
  map_one' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n 1) ∘L (S : homArch σ V₀ hV₀).1 = (S : homArch σ V₀ hV₀).1
    rw [map_one, UnitaryRep.map_one]
    exact ContinuousLinearMap.id_comp _
  map_mul' w w' := by
    refine LinearMap.ext fun S => Subtype.ext ?_
    show σ (finProj K n (w * w')) ∘L (S : homArch σ V₀ hV₀).1 =
      σ (finProj K n w) ∘L (σ (finProj K n w') ∘L (S : homArch σ V₀ hV₀).1)
    rw [map_mul, UnitaryRep.map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

def FinitePartSpace : Type _ := smoothVectors (finRep σ V₀ hV₀)

instance : AddCommGroup (FinitePartSpace σ V₀ hV₀) :=
  inferInstanceAs (AddCommGroup (smoothVectors (finRep σ V₀ hV₀)))

instance : Module ℂ (FinitePartSpace σ V₀ hV₀) :=
  inferInstanceAs (Module ℂ (smoothVectors (finRep σ V₀ hV₀)))

def finitePart : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (FinitePartSpace σ V₀ hV₀) :=
  smoothPart (finRep σ V₀ hV₀)

end MultiplicityOne

end

end GroundTheory.Automorphic
