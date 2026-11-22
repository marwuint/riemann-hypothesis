import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHold
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineFibreHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHolds

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem inputs_of_use :
    ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  intro hII hU hBig hRes
  exact ⟨⟨_root_.GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds, _root_.GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned, _root_.GlobalTheory.CompanionTheory.Ar.Giv.convergenceRate_holds, _root_.GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds, _root_.GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement, _root_.GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds⟩,
    ⟨_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hRes, degree_of_system hII, (hsLinks_of_use hU hBig).1⟩,
    ⟨_root_.GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK hRes, metricLocal⟩,
    ⟨_root_.GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula hII, lineFibre_holds, fibreDim⟩,
    ⟨_root_.GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre.1, _root_.GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre.2, _root_.GlobalTheory.CompanionTheory.Ar.Giv.siuZ⟩⟩

end GlobalTheory.CompanionTheory.Ar.Giv
