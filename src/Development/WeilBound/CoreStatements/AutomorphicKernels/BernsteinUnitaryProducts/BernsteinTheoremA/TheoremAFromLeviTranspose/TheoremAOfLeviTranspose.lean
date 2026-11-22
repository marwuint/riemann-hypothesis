import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGL

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.GelfandKazhdan

namespace PositivityTheory.PfBern.ThmA

section Gen

variable (k : Type) [Field k]

variable {k}

theorem unip_val {n : ℕ} (w : Multiplicative (Fin n → k)) :
    ((unip k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 + colMat k n w.toAdd := rfl

end Gen

section Dist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def conjHomeo {m : ℕ} (g : GL (Fin m) k) : GL (Fin m) k ≃ₜ GL (Fin m) k :=
  (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)

end Dist

end PositivityTheory.PfBern.ThmA

end
