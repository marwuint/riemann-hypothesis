import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

structure Fam (n : ℕ) where
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)

attribute [instance] Fam.nH Fam.iH Fam.cH

end PI.ZuckTensorWork
end
