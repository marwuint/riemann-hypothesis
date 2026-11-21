import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.DampedFunctionalEquationAtPoint

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo.PhkS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable [MeasurableSpace F] [BorelSpace F]

instance instLeft (ψ : AddChar F Circle) : (LFS.vol2 ψ).IsAddLeftInvariant := by
  unfold LFS.vol2
  infer_instance

instance instCompacts (ψ : AddChar F Circle) : IsFiniteMeasureOnCompacts (LFS.vol2 ψ) := by
  unfold LFS.vol2
  infer_instance

end GlobalTheory.CompanionTheory.GJTwo.PhkS

