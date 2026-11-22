import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur

open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RSUnram

noncomputable def hs (α β : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => α ^ (n + 1) + β * hs α β n

theorem hs_zero (α β : ℂ) : hs α β 0 = 1 := rfl

theorem hs_succ (α β : ℂ) (n : ℕ) : hs α β (n + 1) = α ^ (n + 1) + β * hs α β n := rfl

end GlobalTheory.CompanionTheory.RSUnram

end
