import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacGlue

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnimodInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) (h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
      ∫⁻ g, f (g * h) ∂X.measG.μGinf = ∫⁻ g, f g ∂X.measG.μGinf

def WittNear : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a Ω' a₂, IsChart X u' hT Ω a → IsChart X u' hT Ω' a₂ →
    ∀ T ∈ Ω ∩ Ω', IsUnit (a₂ T) → ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')

def GoodChartEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω' a₂, IsChart X u' hT Ω' a₂ ∧ GoodP X u' hT μinf νinf a₂

end PI.AprimeInfW
