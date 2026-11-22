import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProducts
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients

namespace PositivityTheory.Rg.BcN.F2.Final

open PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem hkAlg : HkAlg F ι := _root_.GlobalTheory.CompanionTheory.HeckeAlg.hk_alg F ι
theorem prodFinLen : ProdFinLen F ι := _root_.GlobalTheory.CompanionTheory.ProdLen.prodFinLen F ι
theorem subOfNonNil' : SubOfNonNil' F ι := _root_.GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot F ι

end PositivityTheory.Rg.BcN.F2.Final
