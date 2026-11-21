import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJoint

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.DataInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7}

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

def VIndepAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₁ h₁' →
      IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₂'))

end Formalism.L2.SG.Pf.Carrier
