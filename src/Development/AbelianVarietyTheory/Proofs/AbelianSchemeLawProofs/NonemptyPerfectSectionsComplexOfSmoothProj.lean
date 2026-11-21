import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineChartsStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundle
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem nonempty_perf_of_smooth_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M) := by
  intro R _ X f hf hp M hM
  obtain ⟨H, hH, m, s, hs⟩ := hp
  obtain ⟨K, φ, hK⟩ := _root_.GlobalTheory.Cohom.exists_finite_projective_complex_cechLB R X f H m s M hH hM hs hf
  exact _root_.GlobalTheory.AbLaw.perf_of_projective_model R X f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) K φ hM hs.1
    (GlobalTheory.T.veryAmple_compact_quasiSeparated_affine_charts R X f H m s hH hs).2.2 hK

end GlobalTheory.AbLaw
