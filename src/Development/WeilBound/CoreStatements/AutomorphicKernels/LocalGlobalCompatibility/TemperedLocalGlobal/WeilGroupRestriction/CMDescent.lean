import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace PositivityTheory.Pf1.CLGD.K.CMDescent

section Restrict

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

abbrev res : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[F] Ω) := AlgEquiv.restrictScalarsHom F

@[simp] theorem res_apply (σ : Ω ≃ₐ[E] Ω) (x : Ω) : res F σ x = σ x := rfl

def liftE (τ : Ω ≃ₐ[F] Ω) (h : ∀ e : E, τ (algebraMap E Ω e) = algebraMap E Ω e) : Ω ≃ₐ[E] Ω :=
  { τ.toRingEquiv with commutes' := h }

@[simp] theorem res_liftE (τ : Ω ≃ₐ[F] Ω) (h : ∀ e : E, τ (algebraMap E Ω e) = algebraMap E Ω e) :
    res F (liftE F τ h) = τ := AlgEquiv.ext fun _ ↦ rfl

end Restrict

end PositivityTheory.Pf1.CLGD.K.CMDescent

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC PositivityTheory.Pf1.CLGD.DescRes

namespace PositivityTheory.Pf1.CLGD.K.CMDescent

end PositivityTheory.Pf1.CLGD.K.CMDescent

namespace PositivityTheory.Pf1.CLGD.K

end PositivityTheory.Pf1.CLGD.K
