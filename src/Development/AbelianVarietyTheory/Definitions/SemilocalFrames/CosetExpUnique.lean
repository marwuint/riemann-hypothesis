import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SmallHostRootDiscriminantLe
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AutomorphicArithmetic.MeanSquareBounds.pairEx
import Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
import Development.AutomorphicArithmetic.ShortNorms.typePrimesN
import Development.AutomorphicArithmetic.ShortNorms.levelPrimeN
import Development.AutomorphicArithmetic.ShortNorms.MulLogLeRpowEventually
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

namespace GlobalTheory.Diag.PG.Model

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField

structure Num (R : Ranks) (x eps : ℝ) (Del h : ℕ) : Prop where
  Del_pos : 1 ≤ Del
  hh : R.t + 3 ≤ 2 * h
  x_ge : 1 ≤ x
  third : x ^ (eps / 3) ≤ x ^ eps / 2
  a_le : 4 * x ^ ((11 : ℝ) / 2) ≤ bx x eps
  kx : 2 * (R.k : ℝ) * x ≤ Real.exp (x ^ eps / 2)
  eta_le : 2 * (R.m : ℝ) * h ≤ Real.exp (x ^ eps / 2)
  kDel : 4 * (R.k : ℝ) * Del ≤ Real.exp (x ^ eps / 2)
  eta_log : Real.log (2 * (R.m : ℝ) * h) ≤ x ^ (eps / 4)

variable {R : Ranks} {x eps : ℝ} {Del h : ℕ}

structure Arith (H : Host R) where
  T : ℕ
  T_prime : T.Prime
  hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  ht : THyp H
  hlev : T ∈ H.levelPrimes
  hpde : T ≠ H.pde ∧ T ≠ H.pde'
  pz : 𝓞 H.E
  hK : (pz : H.E) ∈ H.K
  hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E)
  hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}

@[irreducible] def P (n : ℕ) : ℝ := 2 ^ n

end GlobalTheory.Diag.PG.Model

end

namespace GlobalTheory.Diag.PG.DatumModel

end GlobalTheory.Diag.PG.DatumModel

