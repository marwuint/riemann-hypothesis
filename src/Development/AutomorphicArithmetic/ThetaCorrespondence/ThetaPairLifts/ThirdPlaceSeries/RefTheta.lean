import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
def SumPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1
def ReferenceCore : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C
def ReferenceTheta : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C
def ReferenceWeight : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C
end GlobalTheory.RefSum
end
end
