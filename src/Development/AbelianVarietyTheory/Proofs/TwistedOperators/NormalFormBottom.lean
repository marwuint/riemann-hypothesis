import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleMonomialSupportFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleRationalCoefficients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleOpenSubgroupField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleDualAlgebraicityFiniteData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierDegreeBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGfCOfSuppAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RowEx.BotField

theorem field_of_gens {T Hh κ : Type} [Finite T] (v : T → Hh → κ → ℂ) (good : Set Hh)
    (hab : ∃ (H : Finset Hh) (K : Finset κ) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧ (∀ h ∈ H, h ∈ good) ∧
      ∀ t, ∀ h ∈ good, ∀ k, ∃ c : Hh → κ → ℂ, (∀ a b, c a b ∈ M₀) ∧ v t h k = ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * v t h' k')
    (hc : ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, IsAlgebraic ℚ (v t h k / Ω)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, v t h k / Ω ∈ M := by
  obtain ⟨H, K, M₀, hM₀, hH, hv⟩ := hab
  obtain ⟨Ω, hΩ, halg⟩ := hc
  let S : Set ℂ := Set.range fun x : T × H × K => v x.1 x.2.1 x.2.2 / Ω
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hS : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro _ ⟨⟨t, h, k⟩, rfl⟩
    exact (halg t h (hH h h.2) k).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hS
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ S, inferInstance, Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨c, hc, e⟩ := hv t h hh k
  rw [e, Finset.sum_div]
  refine sum_mem fun h' hh' => ?_
  rw [Finset.sum_div]
  refine sum_mem fun k' hk' => ?_
  rw [mul_div_assoc]
  refine mul_mem ((le_sup_left : M₀ ≤ _) (hc h' k')) ((le_sup_right : IntermediateField.adjoin ℚ S ≤ _) ?_)
  exact IntermediateField.subset_adjoin ℚ S ⟨⟨t, ⟨h', hh'⟩, ⟨k', hk'⟩⟩, rfl⟩

theorem sumsIn_mono {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {A A' WW : HSp D}
    {X : Tri T A A' WW} {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SumsIn W σ X)
    (hσ : Set.range σ ⊆ Set.range σ') : SumsIn W σ' X := by
  obtain ⟨Ω, Ω', h0, h0', H⟩ := h
  exact ⟨Ω, Ω', h0, h0', fun t g hg => ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end GlobalTheory.RowEx.BotField

end
