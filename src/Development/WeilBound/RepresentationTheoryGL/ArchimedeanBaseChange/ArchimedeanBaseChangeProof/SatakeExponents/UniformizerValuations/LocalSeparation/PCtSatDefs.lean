import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev tJ {w : Pl E} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (m i : ℕ) : GLw m w :=
  GlobalTheory.WeylGL.tor h0 fun r : Fin m => if (r : ℕ) < i then 1 else 0

abbrev pairsK (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter fun p => p.1 + p.2 = k

end PositivityTheory.Rg.BcB.F.RS
