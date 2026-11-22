import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneOfGapNonneg

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DimLogTop

theorem log_size_le (f r L kap S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hk0 : 0 ≤ kap)
    (hk : Real.log kap ≤ 2 * L) (hfr : Real.log (f * r) ≤ L) (hS0 : 0 ≤ S)
    (hS : S ≤ (f * r * L) ^ 2 * kap + 6 * f * r ^ 2) : Real.log S ≤ 20 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hfr0 : 0 < f * r := by positivity
  have e1 : f * r ≤ Real.exp L := (Real.log_le_iff_le_exp hfr0).1 hfr
  have e2 : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e3 : kap ≤ Real.exp (2 * L) := by
    rcases hk0.eq_or_lt with h0 | h0
    · rw [← h0]; exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp h0).1 hk
  have e4 : (7 : ℝ) ≤ Real.exp (6 * L) := by linarith [Real.add_one_le_exp (6 * L)]
  have hE : Real.exp (6 * L) = Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp (2 * L) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have hE2 : Real.exp L ^ 2 ≤ Real.exp (6 * L) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
  have a1 : (f * r * L) ^ 2 * kap ≤ Real.exp (6 * L) := by
    rw [hE, mul_pow]
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    have : L ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by linarith) e2 2
    gcongr
  have a2 : 6 * f * r ^ 2 ≤ 6 * Real.exp (6 * L) := by
    have : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    nlinarith
  have a3 : S ≤ Real.exp (12 * L) := by
    have : Real.exp (12 * L) = Real.exp (6 * L) * Real.exp (6 * L) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (6 * L)
    nlinarith
  have := (Real.log_le_iff_le_exp h).2 a3
  linarith

theorem cube_le (Cb L Zb : ℝ) (hL : Cb ≤ L) (hL1 : 1 ≤ L) (hZ : L ≤ Zb) : Cb * Zb ^ 3 ≤ Zb ^ 12 := by
  have h1 : 1 ≤ Zb := hL1.trans hZ
  have h9 : Zb ≤ Zb ^ 9 := le_self_pow₀ h1 (by norm_num)
  have h3 : 0 ≤ Zb ^ 3 := by positivity
  calc Cb * Zb ^ 3 ≤ Zb ^ 9 * Zb ^ 3 := mul_le_mul_of_nonneg_right (by linarith) h3
    _ = Zb ^ 12 := by ring

theorem rkK_eq_finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (L : Submodule (𝓞 K) V) (h : Submodule.span K (L : Set V) = ⊤) :
    Formalism.HN.rkK L = Module.finrank K V := by
  unfold Formalism.HN.rkK
  rw [h, finrank_top]

end GlobalTheory.CovTop.DimLogTop

end
