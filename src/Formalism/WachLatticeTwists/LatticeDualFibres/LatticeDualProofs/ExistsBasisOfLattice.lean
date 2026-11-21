import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

universe u

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

open Module

namespace Lat2

end Lat2

open Lat2

namespace Lat2

section Fib

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {VY VT VY' VT' : Type u}
  [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY] [IsScalarTower O (FractionRing O) VY]
  [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']

def pairB (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) :
    (VY × VT) →ₗ[O] (VT' × VY') →ₗ[O] FractionRing O :=
  bY.compl₁₂ (LinearMap.fst O VY VT) (LinearMap.snd O VT' VY') -
    bT.compl₁₂ (LinearMap.snd O VY VT) (LinearMap.fst O VT' VY')

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in
theorem pairB_apply (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (p : VY × VT) (q : VT' × VY') :
    pairB bY bT p q = bY p.1 q.2 - bT p.2 q.1 := rfl

end Fib

end Lat2

end Formalism.RepresentationBoundsCohomology.LOC
