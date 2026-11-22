import Formalism.CoboundaryTransfers.StatementBridge
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.FiniteCocyclesLeCocycles

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

namespace GammaInvariantLatticeLift

section HomPart

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁] [IsScalarTower O A V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂] [IsScalarTower O A V₂]
  {W₁ : WachCohomologyFacts.WachDatum E n V₁} {W₂ : WachCohomologyFacts.WachDatum E n V₂}

def fA (hm : WachCohomologyFacts.Hom W₁ W₂) : (ZMod n → V₁) →ₗ[A] (ZMod n → V₂) :=
  LinearMap.pi (fun j => (hm.f.restrictScalars A).comp (LinearMap.proj j))

end HomPart

end GammaInvariantLatticeLift

end Formalism.CoboundaryTransfers
