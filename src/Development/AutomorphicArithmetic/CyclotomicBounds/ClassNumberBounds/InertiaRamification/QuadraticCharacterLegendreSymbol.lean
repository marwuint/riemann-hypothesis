import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

private noncomputable def quadC (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

private lemma quadC_sq (d : ℕ) [Fact d.Prime] : quadC d ^ 2 = 1 := by
  ext a
  rw [MulChar.pow_apply_coe, quadC, MulChar.ringHomComp_apply, ← map_pow,
    quadraticChar_sq_one a.ne_zero, map_one, MulChar.one_apply_coe]

private lemma quadC_ne (d : ℕ) [Fact d.Prime] (h : d ≠ 2) : quadC d ≠ 1 := by
  rw [quadC, Ne, MulChar.ringHomComp_eq_one_iff (by exact Int.cast_injective)]
  exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact h)

theorem exists_isImagQuad {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (hN : d ∣ N) :
    ∃ ψ : DirichletCharacter ℂ N, IsImagQuad ψ d := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hd2 : d ≠ 2 := by
    rintro rfl
    norm_num at h4
  refine ⟨changeLevel hN (quadC d), ?_, ?_, ?_⟩
  · rw [← map_pow, quadC_sq, map_one]
  · show changeLevel hN (quadC d) (-1) = -1
    have hc := changeLevel_eq_cast_of_dvd' (quadC d) hN (a := -1)
      (by simpa using (isCoprime_one_left (x := (N : ℤ))).neg_left)
    push_cast at hc
    rw [hc, quadC, MulChar.ringHomComp_apply,
      quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; exact hd2), ZMod.card,
      ZMod.χ₄_nat_three_mod_four h4]
    simp
  · rw [conductor_changeLevel]
    rcases hd.eq_one_or_self_of_dvd _ (quadC d).conductor_dvd_level with h1 | h1
    · exact absurd (eq_one_iff_conductor_eq_one.mpr h1) (quadC_ne d hd2)
    · exact h1

end KStar.Ram
