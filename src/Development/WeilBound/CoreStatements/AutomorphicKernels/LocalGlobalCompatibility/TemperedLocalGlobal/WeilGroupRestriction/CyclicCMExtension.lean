import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

open ComplexConjugate

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

end PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

namespace PositivityTheory.Pf1.CLGD.K.CyclicCMExtension.Loc

end PositivityTheory.Pf1.CLGD.K.CyclicCMExtension.Loc

namespace PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

end PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

namespace PositivityTheory.Pf1.CLGD.K

end PositivityTheory.Pf1.CLGD.K
