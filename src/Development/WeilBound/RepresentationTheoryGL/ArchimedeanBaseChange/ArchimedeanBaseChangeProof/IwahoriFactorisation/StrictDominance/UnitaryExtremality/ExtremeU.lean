import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetEigenvectorExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

theorem extremeU : ExtremeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS
  obtain ⟨y, hy, hy1⟩ := _root_.GlobalTheory.CompanionTheory.JacSph.jacNeU L ϖ σ q n V ρ α hU hA hI hS
  obtain ⟨y', ξ, hy', heig, h1⟩ := _root_.GlobalTheory.CompanionTheory.EigTorus.eigU_complete L ϖ σ q n V ρ hU hA y hy hy1
  obtain ⟨lam, hlam0, hne, hlam⟩ := _root_.GlobalTheory.CompanionTheory.EqForm.eqFormU L ϖ σ q n V ρ hU hA ξ y' hy' heig h1
  obtain ⟨β, hβ⟩ := GlobalTheory.T.unitary_character_facts L ϖ σ q n V ρ hU ξ y' hy' heig h1
  obtain ⟨hW, f, hf, hfe⟩ := _root_.GlobalTheory.CompanionTheory.FrobRec.frobU L ϖ σ q n V ρ α hU hA hI hS β lam hlam0 hne
    (fun t ht v => by rw [← hβ t ht]; exact hlam t ht v)
  exact GlobalTheory.T.unitary_chamber_decomposition _root_.GlobalTheory.CompanionTheory.SwapRoot.swapStepU _root_.GlobalTheory.CompanionTheory.InvStep.invStepU L ϖ σ q n hU V ρ hA hI hS.1 α β hW f hf hfe

end PositivityTheory.SphericalProduct

end
