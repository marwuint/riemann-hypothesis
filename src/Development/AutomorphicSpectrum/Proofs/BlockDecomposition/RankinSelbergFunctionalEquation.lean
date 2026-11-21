import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.RankinSelberg

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

instance sFinite_plane_measure (ψ : AddChar F Circle) : SFinite (m2 ψ) := by unfold m2; infer_instance

end Loc

end GlobalTheory.CompanionTheory.RankinSelberg
