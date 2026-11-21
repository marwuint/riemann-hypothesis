import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisG
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparisonStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslation

namespace PositivityTheory.Rg.BcB.D1

theorem mulF : MulF := _root_.GlobalTheory.CompanionTheory.WedgeMinor.mulF
theorem detMono : DetMono := _root_.GlobalTheory.CompanionTheory.DetMonotone.detMono
theorem mulI : MulI := _root_.GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono detMono
theorem wedgeF : WedgeF := GlobalTheory.T.wedge_bound_finite_places mulF
theorem wedgeI : WedgeI := GlobalTheory.T.wedgeI_of_detMono_mulI_var detMono mulI
theorem wedgeSub : WedgeSub := _root_.GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub
theorem pairF : PairF := _root_.GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF mulF
theorem pairI : PairI := _root_.GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono detMono
theorem logAbsBasic : LogAbsBasic := GlobalTheory.T.log_abs_basic_facts
theorem szFin : SzFin := _root_.GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
theorem finSupp : FinSupp := _root_.GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul mulF mulI szFin
theorem degAdelic : DegAdelic := GlobalTheory.T.adelic_degree_formula mulF mulI logAbsBasic finSupp
theorem degBasisG : DegBasisG := GlobalTheory.T.degree_basis_general wedgeF wedgeI mulF mulI logAbsBasic finSupp
theorem degBasis : DegBasis := _root_.GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG degBasisG
theorem degSubmod : DegSubmod := GlobalTheory.T.degree_submodule_bound wedgeF wedgeI wedgeSub finSupp degBasisG GlobalTheory.T.two_bases_comparison
theorem degRat : DegRat := GlobalTheory.T.degree_rational_subspace degBasisG
theorem degMove : DegMove := GlobalTheory.T.degree_under_translation mulF mulI szFin finSupp degBasisG
theorem degBdd : DegBdd := _root_.GlobalTheory.CompanionTheory.DegBound.degBdd_of wedgeF wedgeI mulF mulI szFin finSupp logAbsBasic degBasisG
theorem conjPlaces : ConjPlaces := GlobalTheory.T.conjugate_places_facts
theorem sizeBasic : SizeBasic := _root_.GlobalTheory.CompanionTheory.Size.sizeBasic szFin conjPlaces
theorem degPairing : DegPairing :=
  _root_.GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of wedgeF wedgeI mulF mulI pairF pairI szFin finSupp logAbsBasic conjPlaces degBasisG GlobalTheory.T.radical_subspace_facts
theorem mahler_of_c (h : MahlerC) : Mahler := _root_.GlobalTheory.CompanionTheory.Cutoff.mahler_of degBdd degRat h
theorem mahler : Mahler := mahler_of_c (PositivityTheory.Rg.BcB.E1.mahlerC_of_deg degBasis degAdelic degBdd degRat)
theorem onlyStable : OnlyStable := _root_.GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of degSubmod degMove degBdd degPairing sizeBasic
theorem onlyIsotropic : OnlyIsotropic := GlobalTheory.T.only_isotropic_subspaces onlyStable degPairing sizeBasic
theorem ellTerm : EllTerm := GlobalTheory.T.elliptic_term_of_isotropic onlyIsotropic
theorem chainSum : ChainSum := fun m =>
  ⟨GlobalTheory.T.sign_cone_weight_indicator m, GlobalTheory.T.sign_cone_weight_support_bound m, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.2⟩

end PositivityTheory.Rg.BcB.D1
