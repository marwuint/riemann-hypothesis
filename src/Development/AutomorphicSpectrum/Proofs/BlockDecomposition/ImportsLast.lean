import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadricStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentitiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrability
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactors
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelFibers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOrbitalIntegralUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ D W b₀ hb x₀ hx
  have hDom := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.dom
  have hOF := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.orbFin_of_latBound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq
  have hJ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds
  have hB := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.jnBl
  have hE := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action
  have hS := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.shift
  have hL := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.ikLint
  have hF := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds
  refine ⟨nuT hn I μ x₀, ⟨_root_.GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    _root_.GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, _root_.GlobalTheory.CompanionTheory.ColumnSplitting.continuous_orb_shear hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
