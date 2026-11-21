import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC TensorProduct

namespace GlobalTheory.IntClLocal

theorem isLocalRing_of_isIntegral_of_henselian (O : Type) [CommRing O] [HenselianLocalRing O]
    (S : Type) [CommRing S] [IsDomain S] [Algebra O S] [Algebra.IsIntegral O S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have : Module.Finite O (Algebra.adjoin O {a}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have := GlobalTheory.TameKummer.isLocalRing_of_finite O (Algebra.adjoin O {a})
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨a, Algebra.self_mem_adjoin_singleton O a⟩ : Algebra.adjoin O {a}) with h | h
  · exact Or.inl (h.map (Algebra.adjoin O {a}).val)
  · exact Or.inr (by simpa using h.map (Algebra.adjoin O {a}).val)

end GlobalTheory.IntClLocal
