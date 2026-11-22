import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieVolumeFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUVolBound
theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

end GlobalTheory.SUVolBound
