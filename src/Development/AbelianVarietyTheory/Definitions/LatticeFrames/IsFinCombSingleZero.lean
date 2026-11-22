import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct ComplexOrder MatrixOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Inh

variable {D : D7}

theorem coCpt_of_isDefinite {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) : CoCpt V :=
  GlobalTheory.Unf.Inhab.coCpt_of_isAniso (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hs hd)

theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, h2⟩ := h.2.norm
  have := h2 p hp
  simp [nrm2] at this

end GlobalTheory.SeeSaw.Inh

end
