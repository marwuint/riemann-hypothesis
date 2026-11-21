import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def IsChart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (Ω : Set (HmI X)) (a : HmI X → MfI X) : Prop :=
  Ω ∈ 𝓝 (TI X u' hT) ∧ a (TI X u' hT) = 1 ∧ ContinuousAt a (TI X u' hT) ∧
    ∀ T ∈ Ω, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _)

def PolId {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (μinf : Measure (TupI X)) (νinf : Measure (HmI X))
    (a : HmI X → MfI X) (Ω : Set (HmI X)) (c : HmI X → ENNReal) : Prop :=
  ∀ φ : TupI X → ENNReal, Measurable φ → ∀ S ⊆ Ω, MeasurableSet S →
    ∫⁻ y in gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S) ∩ IndI X, φ y ∂μinf =
      ∫⁻ T in S, c T * ∫⁻ g, φ (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf ∂νinf

def SqChart : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a

end PI.AprimeInfW
