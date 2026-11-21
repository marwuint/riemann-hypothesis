import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (atFin unif IsUnitAt)

namespace GlobalTheory.GaussModulus

variable {E : Type} [Field E] [NumberField E]

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 E)) (z : E) :
    Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 E)) {x : w.adicCompletion E} (hx : Valued.v x ≤ 1) (k : ℕ) :
    ∃ y : 𝓞 E, Valued.v (x - algebraMap E (w.adicCompletion E) (y : E)) ≤ WithZero.exp (-(k : ℤ)) := by
  set c : w.adicCompletion E := algebraMap E _ ((unif w ^ k : Eˣ) : E) with hcdef
  have hvc : Valued.v c = WithZero.exp (-(k : ℤ)) := by
    rw [hcdef, valued_algebraMap, valuation_unif_pow]
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hvc
    exact WithZero.exp_ne_zero hvc.symm
  let U : Set (w.adicCompletion E) :=
    (fun z => c⁻¹ * (z - x)) ⁻¹' ((w.adicCompletionIntegers E) : Set (w.adicCompletion E))
  have hU : IsOpen U := (Valued.isOpen_integer (w.adicCompletion E)).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))
  have hU' : U.Nonempty := ⟨x, by
    simp only [U, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
    exact zero_mem _⟩
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open hU hU'
  have hb' : Valued.v (algebraMap E _ b - x) ≤ WithZero.exp (-(k : ℤ)) := by
    have h1 : Valued.v (c⁻¹ * (algebraMap E _ b - x)) ≤ 1 := hb
    rw [← mul_inv_cancel_left₀ hc0 (algebraMap E _ b - x), map_mul, hvc]
    exact mul_le_of_le_one_right' h1
  have hk1 : WithZero.exp (-(k : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hb1 : w.valuation E b ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) b = (algebraMap E _ b - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ (hb'.trans hk1) hx
  obtain ⟨y, hy⟩ := w.exists_valuation_sub_lt_of_integer hb1 (Units.mk0 (WithZero.exp (-(k : ℤ))) WithZero.exp_ne_zero)
  refine ⟨y, ?_⟩
  have e2 : algebraMap E (w.adicCompletion E) (y : E) - x =
      algebraMap E _ ((y : E) - b) + (algebraMap E _ b - x) := by
    rw [map_sub]
    ring
  rw [Valuation.map_sub_swap, e2]
  refine Valuation.map_add_le _ ?_ hb'
  rw [valued_algebraMap]
  exact hy.le

end GlobalTheory.GaussModulus

end
