import Mathlib
import ReciprocityTheory.DualLattices.WFrobStatement
import ReciprocityTheory.DualLattices.ATowerInh

noncomputable section
open IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 TrivSqZeroExt

namespace GlobalTheory.WModel

instance dualLocal (A : Type) [CommRing A] [IsLocalRing A] : IsLocalRing (DualNumber A) := by
  haveI : Nontrivial (DualNumber A) := (inl_injective (R := A) (M := A)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rw [isUnit_iff_isUnit_fst, isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

variable (p : ℕ) [hp : Fact p.Prime]

instance : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

instance : Fact (1 < p ^ 2) := ⟨Nat.one_lt_pow two_ne_zero hp.out.one_lt⟩

instance zmod_prime_sq_local : IsLocalRing (ZMod (p ^ 2)) :=
  IsLocalRing.of_surjective' (PadicInt.toZModPow (p := p) 2) (ZMod.ringHom_surjective _)

end GlobalTheory.WModel
