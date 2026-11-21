import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.Split

section Lift

variable {F : Type} [Field F] [NumberField F] {d β : F}

def lift (u : Pl F) (x : Q d β (Kp u)) : Q d β (AF F) :=
  ⟨1 + inc u (x.re - 1), inc u x.imI, inc u x.imJ, inc u x.imK⟩

end Lift

end GlobalTheory.CompanionTheory.PlaneSA.Split
