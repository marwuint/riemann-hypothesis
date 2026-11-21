import Mathlib

open TensorProduct

namespace UpperTheory.V.Loc.Thick

variable {Q E B : Type} [Field Q] [Field E] [CommRing B] [Algebra Q E] [Algebra Q B] [Algebra E B]
  [IsScalarTower Q E B] (π : B →ₐ[E] E)

structure Red {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
    (p : X →ₗ[Q] X') (Λ : (B →ₗ[E] E) → X →ₗ[Q] X') : Prop where
  surj : Function.Surjective p
  smul : ∀ a x, p (a • x) = π a • p x
  ker : ∀ x, p x = 0 → x ∈ (RingHom.ker π • ⊤ : Submodule B X)
  form : ∀ (f : B →ₗ[E] E) j, (∀ a, f (a * j) = π a * f j) → ∀ x, Λ f (j • x) = f j • p x

variable {π}

section

variable {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
  {p : X →ₗ[Q] X'} {Λ : (B →ₗ[E] E) → X →ₗ[Q] X'}

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in
theorem Red.desc (h : Red π p Λ) {J J' : Ideal B} {t : B} {f : B →ₗ[E] E} (ht : t ∈ J)
    (hft : f t = 1) (hf : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j) (hJ : ∀ j ∈ J, f j = 0 → j ∈ J')
    {y : X} (hy : y ∈ (J • ⊤ : Submodule B X)) {x : X} (hx : p x = Λ f y) :
    y - t • x ∈ (J' • ⊤ : Submodule B X) := by
  have h1 : ∃ z, p z = Λ f y ∧ y - t • z ∈ (J' • ⊤ : Submodule B X) := by
    refine Submodule.smul_induction_on hy (fun j hj w _ => ⟨algebraMap E B (f j) • w, ?_, ?_⟩) ?_
    · rw [h.smul, h.form f j (hf j hj)]; simp
    · rw [smul_smul, ← sub_smul]
      refine Submodule.smul_mem_smul (hJ _ (J.sub_mem hj (J.mul_mem_right _ ht)) ?_) trivial
      rw [map_sub, mul_comm, hf t ht, hft]; simp
    · rintro a b ⟨z, h1, h2⟩ ⟨w, h3, h4⟩
      refine ⟨z + w, by rw [map_add, map_add, h1, h3], ?_⟩
      convert Submodule.add_mem _ h2 h4 using 1
      rw [smul_add]; abel
  obtain ⟨z, h1, h2⟩ := h1
  have h3 : t • (z - x) ∈ (J' • ⊤ : Submodule B X) := by
    refine Submodule.smul_induction_on (p := fun w => t • w ∈ (J' • ⊤ : Submodule B X))
      (h.ker (z - x) (by rw [map_sub, h1, hx, sub_self])) (fun j hj w _ => ?_) fun a b ha hb => ?_
    · rw [smul_smul]
      refine Submodule.smul_mem_smul (hJ _ (J.mul_mem_right _ ht) ?_) trivial
      rw [mul_comm, hf t ht, RingHom.mem_ker.1 hj, zero_mul]
    · rw [smul_add]; exact Submodule.add_mem _ ha hb
  convert Submodule.add_mem _ h2 h3 using 1
  rw [smul_sub]; abel

variable [IsScalarTower Q B X] [IsScalarTower Q E X']

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] [IsScalarTower Q B X] [IsScalarTower Q E X'] in
theorem Red.comm (h : Red π p Λ) (g : X →ₗ[B] X) (g' : X' →ₗ[E] X') (hg : ∀ x, p (g x) = g' (p x))
    {f : B →ₗ[E] E} {J : Ideal B} (hf : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j)
    {y : X} (hy : y ∈ (J • ⊤ : Submodule B X)) : Λ f (g y) = g' (Λ f y) := by
  refine Submodule.smul_induction_on (p := fun y => Λ f (g y) = g' (Λ f y)) hy (fun j hj w _ => ?_)
    fun a b ha hb => ?_
  · rw [map_smul, h.form f j (hf j hj), h.form f j (hf j hj), map_smul, hg]
  · simp only [map_add, ha, hb]

end

end UpperTheory.V.Loc.Thick
