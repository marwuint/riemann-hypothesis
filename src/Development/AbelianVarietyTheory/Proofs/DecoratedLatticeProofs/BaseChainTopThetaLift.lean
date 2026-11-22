import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorProperty

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem setIntegral_smul_measure_complex {H : Type*} [MeasurableSpace H] (c : ENNReal) (ν : Measure H) (s : Set H) (f : H → ℂ) :
    ∫ y in s, f y ∂(c • ν) = c.toReal • ∫ y in s, f y ∂ν := by
  rw [Measure.restrict_smul, integral_smul_measure]

end GlobalTheory.BaseChain

end
