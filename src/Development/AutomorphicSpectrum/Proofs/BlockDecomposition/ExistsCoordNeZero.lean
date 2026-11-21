import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Relevant

theorem exists_coord_ne_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Ω _ _ y D hP k
  obtain ⟨i, hi⟩ := hP.2.1.2.2 k
  exact ⟨i, fun h0 => hi (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)⟩

end GlobalTheory.CompanionTheory.Ar.Relevant
