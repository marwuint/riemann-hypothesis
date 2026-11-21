import Mathlib
import GroundTheory.LocalFields.DifferentGalois
import GroundTheory.LocalFields.ConductorTransport
import GroundTheory.LocalFields.ConductorMatch

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section OneDim

variable {G : Type*} [Group G]

def charRep (ψ : G →* ℂˣ) : Representation ℂ G ℂ :=
  (DistribMulAction.toModuleEnd ℂ ℂ).comp ψ

@[simp]
theorem charRep_apply (ψ : G →* ℂˣ) (g : G) (v : ℂ) : charRep ψ g v = (ψ g : ℂ) * v :=
  rfl

end OneDim

end GroundTheory.LocalField
