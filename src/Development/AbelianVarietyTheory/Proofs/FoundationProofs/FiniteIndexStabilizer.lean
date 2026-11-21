import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaPowers

theorem cycMod_Ine_surjective (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) :
    Function.Surjective ((cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype) := by
  intro u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hs : Function.Surjective (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) :=
    ZMod.ringHom_surjective _
  haveI := IsLocalHom.of_surjective _ hs
  obtain ⟨v, hv⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hs this u
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
  refine ⟨⟨σ, hσ⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [cycMod, MonoidHom.comp_apply, hσv]
  exact hv

end GlobalTheory.InertiaPowers
