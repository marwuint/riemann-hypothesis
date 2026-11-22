import Development.AutomorphicArithmetic.ShortNorms.SmallOneOf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError

theorem UpperTheory.T3.shortNorm : UpperTheory.T3.ShortNorm := _root_.GlobalTheory.Hk.normPrimes_short_interval_lower

theorem UpperTheory.T3.smallOne : UpperTheory.T3.SmallOne := UpperTheory.T3.smallOne_of _root_.GlobalTheory.Lin.primesRel_holds
