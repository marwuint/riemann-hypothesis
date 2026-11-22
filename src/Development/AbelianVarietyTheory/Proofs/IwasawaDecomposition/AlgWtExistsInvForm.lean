import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
open NumberField

namespace GlobalTheory

theorem algWt_exists_invForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  intro L _ _ _ n a
  exact _root_.GlobalTheory.InvFormBdd.exists_isInvForm L n a

end GlobalTheory
