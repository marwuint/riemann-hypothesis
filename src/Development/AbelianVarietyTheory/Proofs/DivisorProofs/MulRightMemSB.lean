import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJReg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def chiS (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) s

@[simp] theorem chiS_one (ν : kˣ →* ℂˣ) (s : ℂ) : chiS ν s (1 : GL (Fin n) k) = 1 := by
  simp [chiS, gdet]

end GlobalTheory.GJReg
