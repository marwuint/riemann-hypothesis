import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNu

theorem isUnit_of_generates {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
    {k : ℕ} {α : D.toPre.X} {s t : D.toPre.SecB k α} (hs : SecBGenerates k α s) {a : R}
    (h : SecIsMul D.toPre.P.A.hom a s t) : IsUnit a := by
  obtain ⟨b, hb, -⟩ := hs t
  have h₁ : SecIsMul D.toPre.P.A.hom 1 s s := fun j => by simp only [scal, resTop, map_one, _root_.one_mul]
  have h₂ : SecIsMul D.toPre.P.A.hom (a * b) s s := fun j => by
    conv_lhs => rw [h j, hb j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  exact IsUnit.of_mul_eq_one b ((hs s).unique h₂ h₁)

end GlobalTheory.ThetaNu
