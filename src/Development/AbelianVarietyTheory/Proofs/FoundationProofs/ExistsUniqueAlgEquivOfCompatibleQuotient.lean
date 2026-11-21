import Mathlib

noncomputable section

namespace GlobalTheory

open TensorProduct

theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := isPrecomplete_of_finite I M

theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

end GlobalTheory
