import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

def extTensorEquiv {G H V W V' W' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W} {ρ' : Representation ℂ G V'}
    {σ' : Representation ℂ H W'} (φ : ρ.Equiv ρ') (ψ : σ.Equiv σ') :
    (extTensor ρ σ).Equiv (extTensor ρ' σ') :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (ψ.toIntertwiningMap.isIntertwining _ _ g.2 w)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.SmGL.RowOneCell
