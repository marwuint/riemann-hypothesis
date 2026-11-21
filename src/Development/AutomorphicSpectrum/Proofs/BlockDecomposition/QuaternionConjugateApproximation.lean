import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.HermitianNormLocal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
import GroundTheory.AutomorphicForms.HermitianBinaryValues

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.KeyApprox

variable {F : Type} [Field F] [NumberField F]

theorem rat_re {d β : F} {R : Type} [CommRing R] [Algebra F R] (x : Q d β F) :
    (rat x : Q d β R).re = algebraMap F R x.re := rfl

end GlobalTheory.CompanionTheory.PlaneSA.KeyApprox
