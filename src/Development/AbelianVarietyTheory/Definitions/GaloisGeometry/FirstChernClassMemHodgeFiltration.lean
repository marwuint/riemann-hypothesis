import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.LogCris.CupModel

variable {b : Base} {L : b.Fun}

theorem isNilpotent_of_mem (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    simpa using this
  · obtain ⟨n, hn⟩ := T.adm.1 hp
    refine ⟨b.p ^ n, ?_⟩
    rw [← T.δ.factorial_mul_dpow_eq_pow hx]
    obtain ⟨c, hc⟩ : b.p ^ n ∣ (b.p ^ n).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero _ hp)) le_rfl
    rw [hc, Nat.cast_mul, Nat.cast_pow, hn, zero_mul, zero_mul]

end GlobalTheory.LogCris.CupModel

namespace GlobalTheory.CatH

end GlobalTheory.CatH
