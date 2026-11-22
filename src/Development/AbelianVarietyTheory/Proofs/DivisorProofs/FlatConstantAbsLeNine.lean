import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.TwistDeg

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem logSum_bad_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) :
    logSum (GlobalTheory.FlatTw.badPrimes H l) ≤ Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hd := H.d_prime.ne_zero
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd) hD) hM
  have h0 : ∀ p ∈ (2 * H.d * (discr E).natAbs * l.M').primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' =
      Real.log ((2 * H.d * (discr E).natAbs * l.M' : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]
  rw [e, logSum, GlobalTheory.FlatTw.badPrimes, ← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Nat.prod_primeFactors_dvd _))
  exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem lrd_eq (E : Type) [Field E] [NumberField E] :
    lrd E = Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := by
  have h : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  rw [lrd, rootDiscr_def, Int.cast_abs, Real.log_rpow h, div_eq_inv_mul]

theorem numeric {f r L q a b s c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hq : q ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * L) (hs0 : 0 ≤ s) (hs : s ≤ 6 * f * r) (hc : |a| ≤ 9 * r * L * s)
    (hB : c ≤ 1 + 2 * b + 2 * f * b + 30 * L) : -(120 * (f * r * L) ^ 2) ≤ a - q * b * s - c := by
  have h1 : q * b * s ≤ r * (3 * L) * (6 * f * r) := by gcongr
  have h2 : 9 * r * L * s ≤ 9 * r * L * (6 * f * r) := by gcongr
  have h3 : f * b ≤ f * (3 * L) := by gcongr
  have h4 : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    rw [show (f * r * L) ^ 2 = f * r ^ 2 * L * (f * L) by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hf hL)
  have h5 : f * L ≤ f * r ^ 2 * L := by
    rw [show f * r ^ 2 * L = f * L * r ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
  have h6 : L ≤ f * L := le_mul_of_one_le_left (by positivity) hf
  have h7 := (abs_le.1 hc).1
  nlinarith

end GlobalTheory.TwistDeg
