import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.CompanionTheory.SegFine2 (seg2)

namespace GlobalTheory.CompanionTheory.SegZRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_segLow (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (i : Fin (segLow Δ a h0).len) :
    (segLow Δ a h0).term i = Δ.first.nu (((i : ℕ) : ℕ) : ℂ) := rfl

end GlobalTheory.CompanionTheory.SegZRep

end
