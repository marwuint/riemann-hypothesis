import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l ((discr E).natAbs.factorization l) (ordCompl[l] (discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hspan0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  rw [multiplicity_eq_count_normalizedFactors hirr differentIdeal_ne_bot,
    multiplicity_eq_count_normalizedFactors hirr hspan0, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement
