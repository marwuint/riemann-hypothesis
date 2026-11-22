import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CuspStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def prod₂MapR {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π₁ : Representation ℂ (GL (Fin r) k) U)
    {π₂ : Representation ℂ (GL (Fin t) k) X} {π₂' : Representation ℂ (GL (Fin t) k) Y}
    (f : π₂.IntertwiningMap π₂') : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁ π₂') :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁ π₂')
    ⟨TensorProduct.map LinearMap.id f.toLinearMap, fun g => by
      ext u x
      exact congrArg (fun b => π₁ g.1 u ⊗ₜ[ℂ] b) (f.isIntertwining _ _ g.2 x)⟩ _)

def prod₂MapL {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {π₁ : Representation ℂ (GL (Fin r) k) X}
    {π₁' : Representation ℂ (GL (Fin r) k) Y} (f : π₁.IntertwiningMap π₁')
    (π₂ : Representation ℂ (GL (Fin t) k) U) : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁' π₂) :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁' π₂)
    ⟨TensorProduct.map f.toLinearMap LinearMap.id, fun g => by
      ext x u
      exact congrArg (fun b => b ⊗ₜ[ℂ] π₂ g.2 u) (f.isIntertwining _ _ g.1 x)⟩ _)

end GlobalTheory.CompanionTheory.CuspStd
