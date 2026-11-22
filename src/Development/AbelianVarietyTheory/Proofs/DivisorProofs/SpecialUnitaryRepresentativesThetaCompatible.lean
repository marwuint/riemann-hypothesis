import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLatticeStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hv : v ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  GlobalTheory.T.frameStabiliser_mapsTo_completedLattice β Λ hβ x hx v hv

theorem mulVec_mem_hat (D : D7) {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (k : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hk : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St β)
    (x : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (hx : x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    k.1 *ᵥ x ∈
      GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ x hx
  have h2 := mulVec_mem_hatL β Λ hβ _ hk _ h1
  have h3 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h2
  convert h3 using 1
  funext a
  simp only [Matrix.mulVec, dotProduct, Formalism.UG.bc, Formalism.IndefR.Lev.swapAE, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul]
  simp

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
end GlobalTheory.MassLinkConj
