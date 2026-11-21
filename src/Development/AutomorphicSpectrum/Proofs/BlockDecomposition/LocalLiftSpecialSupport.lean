import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.LiftSupp

section Tensor

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def pB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem iB_tmul (P : PlaceMap F K) (a : K) (b : E) : iB P (a ⊗ₜ[F] b) = P.inj a ⊗ₜ[F] b := rfl

theorem pB_tmul (P : PlaceMap F K) (a : AF F) (b : E) : pB P (a ⊗ₜ[F] b) = P.proj a ⊗ₜ[F] b := rfl

end Tensor

end GlobalTheory.CompanionTheory.SaGen.LiftSupp
