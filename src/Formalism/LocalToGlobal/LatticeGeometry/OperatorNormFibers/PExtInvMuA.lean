import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvMu

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section Ext

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']

abbrev e1 (A : HLat K) (x : A.V) : (baseChange K' A).V := ((1 : K') ⊗ₜ[K] x : K' ⊗[K] A.V)

theorem ext_eq (A : HLat K) (N : Submodule (𝓞 K) A.V) :
    ext K' A N = Submodule.span (𝓞 K') (e1 K' A '' (N : Set A.V)) := rfl

end Ext

end Formalism.L2.Geo.ExtensionFiltration.ExtInvMu
