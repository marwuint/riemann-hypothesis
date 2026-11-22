import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def WhitRankStd : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
    Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1

end GlobalTheory.BZSeg

end
