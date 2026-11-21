import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.ArchimedeanLeaf.LeafARCHFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open GlobalTheory.NormSum

namespace GlobalTheory.NormSum.Compare

theorem sqrt_le_rd (D : D7) : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem three_le (D : D7) : (3 : ℝ) ≤ D.host.q ∧ (3 : ℝ) ≤ D.host.d := by
  obtain ⟨hq, hd, -, hq2, hd2⟩ := D.host.hypOdd
  have := hq.two_le
  have := hd.two_le
  constructor
  · exact_mod_cast (show 3 ≤ D.host.q by omega)
  · exact_mod_cast (show 3 ≤ D.host.d by omega)

theorem log_d_le (D : D7) : Real.log D.host.d ≤ 2 * Real.log D.host.rdE := by
  obtain ⟨hq, hd⟩ := three_le D
  have h2 := sqrt_le_rd D
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity)
  have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have h5 : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by nlinarith
  have := Real.log_le_log (by linarith) h5
  rwa [Real.log_pow, Nat.cast_ofNat] at this

end GlobalTheory.NormSum.Compare
