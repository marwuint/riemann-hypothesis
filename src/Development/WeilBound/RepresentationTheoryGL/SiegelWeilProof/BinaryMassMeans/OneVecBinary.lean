import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMulStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrinciple
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  _root_.GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula (_root_.GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant _root_.GlobalTheory.CompanionTheory.MassCocompact.coCpt _root_.GlobalTheory.CompanionTheory.SW.LocBin.locMass) _root_.GlobalTheory.CompanionTheory.SW.MassSimil.simil _root_.GlobalTheory.CompanionTheory.SW.MassHasse.hasse
    (_root_.GlobalTheory.CompanionTheory.RgMass.cnt _root_.GlobalTheory.CompanionTheory.SW.MassTest.testEx (_root_.GlobalTheory.CompanionTheory.SW.LS.lside GlobalTheory.T.equidistribution _root_.GlobalTheory.CompanionTheory.MassCocompact.coCpt)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (_root_.GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd GlobalTheory.T.equidistribution GlobalTheory.T.counting_bound_alt) _root_.GlobalTheory.CompanionTheory.SW.LocBin.locMass))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
