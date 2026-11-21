import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

noncomputable section

namespace GlobalTheory.EtC.Bock.RedSpec
open GlobalTheory.EtC

variable (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ)

def primRed {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q A).2.2.2.2.2 q hq ζ
    rw [← h]; exact ξ.2⟩

theorem primRed_val {A : Type} [CommRing A] (ζ : Prim Q A) : (primRed Q q hq ζ).1 = ζ.1 ^ (Q / q) := rfl

end GlobalTheory.EtC.Bock.RedSpec

namespace GlobalTheory.EtC.Bock.RedSpec
end GlobalTheory.EtC.Bock.RedSpec
