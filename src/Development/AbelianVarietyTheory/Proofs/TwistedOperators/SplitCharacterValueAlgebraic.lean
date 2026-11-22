import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInterOfSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCharAlg

open Formalism.L2.Host
open scoped TensorProduct

theorem isAlgebraic_loc {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {n : I → ℤ}
    {χ : HChar E} (h : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    IsAlgebraic ℚ ((χ.loc v x : ℂˣ) : ℂ) := by
  have h2 : (χ ^ 2).HasInf φ (fun i => 2 * n i) := by
    intro k
    have e1 : (((χ ^ 2).inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) ^ 2 := rfl
    rw [e1, h k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = _ ^ (2 * n i)
    rw [mul_comm, zpow_mul]
    norm_cast
  obtain ⟨M, hM, hv⟩ := GlobalTheory.HeckeLocVals.locVals_of_even h2
  have hx := hv v x
  have e2 : (((χ ^ 2).loc v x : ℂˣ) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) ^ 2 := rfl
  rw [e2] at hx
  have hint : IsIntegral ℚ (((⟨_, hx⟩ : M) : ℂ)) := (IsIntegral.of_finite ℚ (⟨_, hx⟩ : M)).map M.val
  exact IsAlgebraic.of_pow two_pos hint.isAlgebraic

open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem exists_locIdele {D : D7} {e : AE D} (he : IsSplitIdem D e) (x : (AE D)ˣ) (hx : (x : AE D) = e * x + (1 - e)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ), x = GlobalTheory.LFun.locIdele D.host.F w y := by
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 he
  have hA : At (evFin D.host.F v) (splitIdemAd (isCMExt_host D) τ) := by
    intro u hu
    rw [Algebra.smul_def, mul_comm]
    change singleTens D.host.E v _ * _ = 0
    rw [singleTens_mul]
    have : compFin D.host.F D.host.E v (algebraMap (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) u) = 0 := by
      change (evFin D.host.F v u) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [hu, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  have h1 : (x : AE D) - 1 = splitIdemAd (isCMExt_host D) τ * ((x : AE D) - 1) := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [hx]
    ring
  refine ⟨_, _, GlobalTheory.ChrLocal.eq_locIdele_splitPrime (isCMExt_host D) τ x ?_ ?_⟩
  · intro u hu
    rw [h1, ← smul_mul_assoc, hA u hu, zero_mul]
  · obtain ⟨-, e0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd (isCMExt_host D) τ
    rw [hx, map_add, map_mul, map_sub, map_one, e0]
    ring

end GlobalTheory.SplitCharAlg

namespace GlobalTheory.SplitCharAlg

end GlobalTheory.SplitCharAlg
