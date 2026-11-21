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

theorem cupC_one_one_model {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ ModuleCat.{0} R} (μ : Mult F)
    (f g : Cn F 1) (s : ComposableArrows C 2) :
    cupC μ (show 1 + 1 = 2 from rfl) f g s =
      μ.mul _ ((F.map (s.map' 1 2)).hom (f ((fr_mono 1 2 (by omega)).functor ⋙ s)))
        ((F.map (s.map' 2 2)).hom (g ((bk_mono 1 1 2 (by omega)).functor ⋙ s))) := rfl

end GlobalTheory.CatH
