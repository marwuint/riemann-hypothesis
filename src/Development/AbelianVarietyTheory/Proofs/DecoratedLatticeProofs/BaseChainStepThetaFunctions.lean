import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

variable {D : D7}

theorem rank_Yc_le_succ (j : ℕ) : (Yc D j).rank ≤ (Yc D (j + 1)).rank := by
  rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.Y_rank _ (min_le_right _ _)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_min_right D.R.m (Nat.le_succ j))) _

end GlobalTheory.BaseChain

end
