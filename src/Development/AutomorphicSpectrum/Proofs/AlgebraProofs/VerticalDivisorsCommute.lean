import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisor

namespace GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem verticalDivisorsCommute : VerticalDivisorsCommute.Statement.{0} :=
  VerticalDivisorsCommute.proof _root_.GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main Representative.full
    IntNumAddFirst.full DivCycleFiniteSupport.full MinimalPrimeMultiHomog.full
    SupSpanMultiHomog.full SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full
    DimStrictDrop.full

end GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors
