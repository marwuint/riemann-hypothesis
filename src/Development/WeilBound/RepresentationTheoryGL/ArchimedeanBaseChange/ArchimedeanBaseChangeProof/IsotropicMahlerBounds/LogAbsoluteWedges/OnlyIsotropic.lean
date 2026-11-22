import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisG
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslation

namespace PositivityTheory.Rg.BcB.D1

theorem mulF : MulF := _root_.GlobalTheory.CompanionTheory.WedgeMinor.mulF
theorem detMono : DetMono := _root_.GlobalTheory.CompanionTheory.DetMonotone.detMono
theorem mulI : MulI := _root_.GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono detMono
theorem wedgeF : WedgeF := _root_.GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF mulF
theorem wedgeI : WedgeI := _root_.GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI detMono mulI
theorem wedgeSub : WedgeSub := _root_.GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub
theorem pairF : PairF := _root_.GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF mulF
theorem pairI : PairI := _root_.GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono detMono
theorem logAbsBasic : LogAbsBasic := _root_.GlobalTheory.CompanionTheory.LogAbs.logAbsBasic
theorem szFin : SzFin := _root_.GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
theorem finSupp : FinSupp := _root_.GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul mulF mulI szFin
theorem degAdelic : DegAdelic := GlobalTheory.T.adelic_degree_formula mulF mulI logAbsBasic finSupp
theorem degBasisG : DegBasisG := _root_.GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of wedgeF wedgeI mulF mulI logAbsBasic finSupp
theorem degBasis : DegBasis := _root_.GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG degBasisG
theorem degSubmod : DegSubmod := GlobalTheory.T.degree_submodule_bound wedgeF wedgeI wedgeSub finSupp degBasisG _root_.GlobalTheory.CompanionTheory.LinAlg.twoBases
theorem degRat : DegRat := _root_.GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG degBasisG
theorem degMove : DegMove := _root_.GlobalTheory.CompanionTheory.DegMoveProof.degMove_of mulF mulI szFin finSupp degBasisG
theorem degBdd : DegBdd := _root_.GlobalTheory.CompanionTheory.DegBound.degBdd_of wedgeF wedgeI mulF mulI szFin finSupp logAbsBasic degBasisG
theorem conjPlaces : ConjPlaces := GlobalTheory.T.conjugate_places_facts
theorem sizeBasic : SizeBasic := _root_.GlobalTheory.CompanionTheory.Size.sizeBasic szFin conjPlaces
theorem degPairing : DegPairing :=
  _root_.GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of wedgeF wedgeI mulF mulI pairF pairI szFin finSupp logAbsBasic conjPlaces degBasisG _root_.GlobalTheory.CompanionTheory.RadicalForm.radical
theorem mahler_of_c (h : MahlerC) : Mahler := _root_.GlobalTheory.CompanionTheory.Cutoff.mahler_of degBdd degRat h
theorem mahler : Mahler := mahler_of_c (PositivityTheory.Rg.BcB.E1.mahlerC_of_deg degBasis degAdelic degBdd degRat)
theorem onlyStable : OnlyStable := _root_.GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of degSubmod degMove degBdd degPairing sizeBasic
theorem onlyIsotropic : OnlyIsotropic := _root_.GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of onlyStable degPairing sizeBasic
theorem ellTerm : EllTerm := _root_.GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic onlyIsotropic
theorem chainSum : ChainSum := fun m =>
  ⟨_root_.GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator m, _root_.GlobalTheory.CompanionTheory.SignChain.gam_support m, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.2⟩

end PositivityTheory.Rg.BcB.D1
