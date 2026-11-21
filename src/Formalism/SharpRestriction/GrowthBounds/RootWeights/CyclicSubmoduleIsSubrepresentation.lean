import Formalism.SharpRestriction.GrowthBounds.RootWeights.OperatorsKillInvariantProjection

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem charZero_fraction_field_of_setting {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  have hO : CharZero O := by
    rcases S with ⟨w, hw, hpm, hp0, -⟩
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      have hne : p ≠ ringChar O := by
        rintro h
        apply hp0
        rw [h]
        exact CharP.cast_eq_zero O (ringChar O)
      have hcop : Nat.gcd p (ringChar O) = 1 := (Nat.coprime_primes hp hq).mpr hne
      have key : (1 : O) = (p : O) * (Nat.gcdA p (ringChar O) : O) := by
        have h := congrArg (fun z : ℤ => (z : O)) (Nat.gcd_eq_gcd_ab p (ringChar O))
        simp only [hcop, Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h
        exact h
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := key ▸ Ideal.mul_mem_right _ _ hpm
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · haveI : CharP O 0 := hq ▸ ringChar.charP O
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

theorem cyclicSubmodule_isSubrepresentation {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (v : V) :
    IsSubrepresentation E (cyclicSubmodule E v) := by
  unfold IsSubrepresentation cyclicSubmodule
  intro a b x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem log_bound_monotone (p n : ℕ) {k l : ℕ} (h : k ≤ l) : deF p n k ≤ deF p n l := by
  unfold deF
  exact Nat.log_mono_right (by omega)

theorem pow_smul_mem_of_le' {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (M : Submodule O W) (c : O) {a b : ℕ}
    (hab : a ≤ b) {z : W} (h : c ^ a • z ∈ M) : c ^ b • z ∈ M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul]
  exact M.smul_mem _ h

end Formalism.MainNotions.G.GLWeightTheory
