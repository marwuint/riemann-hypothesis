import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.EigenLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]

def tensAct (ρ : orderC c →+* Module.End O H) : orderC c ⊗[ℤ] O →ₗ[ℤ] Module.End O H :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : orderC c) (x : O) => x • ρ a)
    (fun a b x => by simp [map_add, smul_add])
    (fun n a x => by rw [map_zsmul, smul_comm])
    (fun a x y => by simp [add_smul])
    (fun n a x => smul_assoc n x (ρ a)))

end GlobalTheory.EigenLattice
