import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovHt
def ShortAlt : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → ShortAt p i Y PP C u1
def GeometricCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → GeomAt p i Y u1
def MultiplicityConstantCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → MultAt p i Y PP C u1
def ErrorBudgetCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → BudgetAt p i Y PP C u1
end GlobalTheory.CovHt
end
end
