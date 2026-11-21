import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.ExLift

section Tens

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (a : K) (e : E) :
    iB P (a ⊗ₜ[F] e : K ⊗[F] E) = P.inj a ⊗ₜ[F] e := rfl

end Tens

end GlobalTheory.CompanionTheory.SaGen.ExLift

namespace GlobalTheory.CompanionTheory.SaGen.ExLift

end GlobalTheory.CompanionTheory.SaGen.ExLift
