import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_pos_nat_clearing_rat_denominators {κ : Type} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ z : ℤ, (M : ℚ) * q k = z := by
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).pos, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
  refine ⟨m * (q k).num, ?_⟩
  rw [hm]
  push_cast
  calc ((q k).den : ℚ) * m * q k = m * (q k * (q k).den) := by ring
    _ = m * (q k).num := by rw [Rat.mul_den_eq_num]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.adelicPair_elementary : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), _root_.GlobalTheory.ClassFin.AdelicPair R R₀ → (∀ M : ℕ, 0 < M → ∀ r ∈ R₀, ∃ z : ℤ, ∃ a ∈ R₀, r = (z : R) + (M : R) * a) ∧ (∀ (κ : Type) [Fintype κ] (r : κ → R), ∃ M : ℕ, 0 < M ∧ ∀ k, (M : R) * r k ∈ R₀) ∧ Function.Injective (algebraMap ℚ R) := by
  intro R _ _ R₀ hR
  refine ⟨fun M hM r hr => ?_, fun κ _ r => ?_, ?_⟩
  · obtain ⟨q, a, ha, hra⟩ := hR.approx M hM r
    have hq : algebraMap ℚ R q ∈ R₀ := by
      have h : algebraMap ℚ R q = r - (M : R) * a := by rw [hra]; ring
      rw [h]
      exact R₀.sub_mem hr (R₀.mul_mem (natCast_mem R₀ M) ha)
    obtain ⟨z, rfl⟩ := hR.int_of_mem q hq
    exact ⟨z, a, ha, by rw [hra, map_intCast]⟩
  · choose q a ha hra using fun k => hR.approx 1 one_pos (r k)
    obtain ⟨M, hM, hMq⟩ := exists_pos_nat_clearing_rat_denominators q
    refine ⟨M, hM, fun k => ?_⟩
    obtain ⟨z, hz⟩ := hMq k
    have h : (M : R) * r k = (z : R) + (M : R) * a k := by
      rw [hra k, Nat.cast_one, one_mul, mul_add, ← map_natCast (algebraMap ℚ R) M, ← map_mul, hz,
        map_intCast]
    rw [h]
    exact R₀.add_mem (intCast_mem R₀ z) (R₀.mul_mem (natCast_mem R₀ M) (ha k))
  · have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := hR.int_of_mem (1 / 2)
        (by rw [Subsingleton.elim (algebraMap ℚ R (1 / 2)) 0]; exact R₀.zero_mem)
      have h2 : (1 : ℚ) = 2 * z := by rw [← hz]; norm_num
      have h3 : (1 : ℤ) = 2 * z := by exact_mod_cast h2
      omega
    exact (algebraMap ℚ R).injective

end GlobalTheory.ClassFin
