import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Functional

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}

variable (μ σ) in

def cuspIntertwiners : Submodule ℂ (H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)) where
  carrier := {T | T ∈ σ.intertwiners (rightRegularRep Γ₁ μ) ∧ ∀ v, T v ∈ cuspidalL2 μ}
  add_mem' hS hT := ⟨add_mem hS.1 hT.1, fun v => add_mem (hS.2 v) (hT.2 v)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ hT := ⟨Submodule.smul_mem _ c hT.1, fun v => Submodule.smul_mem _ c (hT.2 v)⟩

open Classical in
variable (μ σ) in

def whittakerAt (T : cuspIntertwiners μ σ) (w : H) : ℂ :=
  if h : ∃ F, HasContRep μ (T.1 w) F then whittakerOne h.choose 1 else 0

end MultiplicityOne

end

end GroundTheory.Automorphic
