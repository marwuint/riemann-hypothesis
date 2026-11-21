import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

structure P4 {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (ι D R P ρ κ : Type)
    [AddCommGroup D] [Module O D] [CommRing R] [Algebra O R] [AddCommGroup P] [Module O P] where
  lt : ρ → ι
  t : R
  γR : R →ₐ[O] R
  locA : ρ → A →+* R
  loc : ρ → D →ₗ[O] P
  γl : ρ → P →ₗ[O] P
  n : ρ → κ → P
  a : ρ → κ → ℤ

end Formalism.RepresentationBoundsCohomology.JN
