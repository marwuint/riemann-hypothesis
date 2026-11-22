import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

end GlobalTheory.SeeSaw.ChainIdeals
