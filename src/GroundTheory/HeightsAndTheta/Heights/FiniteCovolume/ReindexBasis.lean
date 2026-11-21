import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.Reindex

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def reGL (e : ι ≃ κ) : GL ι ℂ →* GL κ ℂ :=
  Units.map (Matrix.reindexRingEquiv ℂ e).toMonoidHom

theorem coe_reGL (e : ι ≃ κ) (g : GL ι ℂ) :
    ((reGL e g : GL κ ℂ) : Matrix κ κ ℂ) = reindex e e (g : Matrix ι ι ℂ) := rfl

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

variable [NumberField E]

variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.Reindex
