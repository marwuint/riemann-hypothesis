import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechPer.isPer_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  intro A _ g L u x q q' hq hq'
  have h := ((_root_.GlobalTheory.CechPer.periods_linear A g L u).1 x x q q' hq hq').2
  rw [sub_self] at h
  exact sub_eq_zero.mp (_root_.GlobalTheory.CechPer.zero_periods_eq_zero A g L u _ h)
