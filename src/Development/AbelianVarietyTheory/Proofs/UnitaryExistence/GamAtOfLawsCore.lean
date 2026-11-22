import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore' : ∀ (D : D7) (T : Core D), LawsCore T → GlobalTheory.RunIn.GamAt T :=
  fun D T h j hj σ hσ => _root_.GlobalTheory.PrincCore.hasPrinc_core D T h j hj σ hσ

end GlobalTheory.RunIn
