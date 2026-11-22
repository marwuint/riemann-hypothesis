import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.SegmentRepModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Concl {d : ℕ} (σ : Representation ℂ (GL (Fin d) k) V) (l : ℕ) : Prop :=
  ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
    S.toRepresentation.IsIrreducible ∧
    (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      S'.toRepresentation.IsIrreducible → S' = S) ∧
    Nonempty ((jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ l)))

end GlobalTheory.SegmentRepModel

end
