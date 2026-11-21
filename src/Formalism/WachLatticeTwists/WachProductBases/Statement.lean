import Formalism.WachLatticeTwists.WachProductBases.OneAddPowSubOne
import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

structure NData (S : HidaSetting O A) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] where
  N : ι → Submodule A D
  φ : ι → D →ₗ[O] D
  γ : ι → D →ₗ[O] D
  φ_smul : ∀ (i : ι) (a : A) (x : D), φ i (a • x) = S.φ a • φ i x
  γ_smul : ∀ (i : ι) (a : A) (x : D), γ i (a • x) = S.γ a • γ i x
  comm : ∀ (i : ι) (x : D), φ i (γ (pr i) x) = γ i (φ i x)
  X_bij : Function.Bijective (fun x : D => S.X • x)
  Q_bij : Function.Bijective (fun x : D => S.Q • x)
  etale : ∀ i : ι, Function.Bijective
    (fun m : Fin S.ℓ → D => ∑ j : Fin S.ℓ, S.ε ^ (j : ℕ) • φ i (m j))

namespace NData

end NData

end Formalism.RepresentationBoundsCohomology.N1
