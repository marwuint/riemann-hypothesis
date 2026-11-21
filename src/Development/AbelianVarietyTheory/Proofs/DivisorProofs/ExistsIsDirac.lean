import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section
open NumberField MeasureTheory Matrix Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutGrowth.ApproxId GlobalTheory.GLFin
open scoped ContDiff

namespace GlobalTheory.GLFin.Inhab
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in

theorem contDiffOn_invL : ContDiffOn ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  intro x hx
  have hu : IsUnit (S x) := hx
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (S x) := by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 := (T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)
  refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)
end

end GlobalTheory.GLFin.Inhab
end
