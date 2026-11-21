import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Fc

def Lg1 (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (r : V4.Slot → Prop) : Prop :=
  ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ r (sAnd Q' R)

end GlobalTheory.Fc

end
