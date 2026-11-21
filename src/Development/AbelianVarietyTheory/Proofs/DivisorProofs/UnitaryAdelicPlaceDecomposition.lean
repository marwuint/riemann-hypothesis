import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryPlaceSplit

theorem mix_mul {S A : Type} [CommRing S] [Ring A] [Algebra S A] {e : S} (he : e * e = e) (x y z w : A) :
    (e • x + (1 - e) • y) * (e • z + (1 - e) • w) = e • (x * z) + (1 - e) • (y * w) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h0, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, zero_smul, add_zero,
    zero_add]

variable {F : Type} [Field F] [NumberField F]

def idemAt (v : Pl F) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

end GlobalTheory.UnitaryPlaceSplit

end

namespace GlobalTheory.UnitaryPlaceSplit

end GlobalTheory.UnitaryPlaceSplit
