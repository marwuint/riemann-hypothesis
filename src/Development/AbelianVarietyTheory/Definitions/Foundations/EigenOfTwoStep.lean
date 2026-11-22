import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

namespace SSAdm

variable {R : Type} [CommRing R] {A : Set Letter}

variable {M : Type} [AddCommGroup M] [Module R M]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
variable {R : Type} [CommRing R] {A : Set _root_.GlobalTheory.KZ.Letter} in
variable {M : Type} [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.SSAdm.lift_sub_smul_mem {f : _root_.GlobalTheory.KZ.Letter → Module.End R M}
    {lam : _root_.GlobalTheory.KZ.Letter → R} {W : Submodule R M}
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) {x : M} (hx : ∀ T ∈ A, f T x - lam T • x ∈ W)
    {P : FreeAlgebra R _root_.GlobalTheory.KZ.Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
  have key : ∀ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A),
      (∀ y ∈ W, FreeAlgebra.lift R f P y ∈ W) ∧
        FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
    intro P hP
    induction hP using Algebra.adjoin_induction with
    | mem P hP =>
      obtain ⟨T, hT, rfl⟩ := hP
      simp only [FreeAlgebra.lift_ι_apply]
      exact ⟨hW T hT, hx T hT⟩
    | algebraMap r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact ⟨fun y hy => W.smul_mem r hy, W.zero_mem⟩
    | add P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_add, LinearMap.add_apply]
        exact W.add_mem (hP.1 y hy) (hQ.1 y hy)
      · convert W.add_mem hP.2 hQ.2 using 1
        simp only [map_add, LinearMap.add_apply, add_smul]
        abel
    | mul P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_mul, Module.End.mul_apply]
        exact hP.1 _ (hQ.1 y hy)
      · convert W.add_mem (hP.1 _ hQ.2) (W.smul_mem (FreeAlgebra.lift R lam Q) hP.2) using 1
        simp only [map_mul, Module.End.mul_apply, map_sub, LinearMap.map_smul, smul_sub,
          smul_smul]
        rw [mul_comm (FreeAlgebra.lift R lam Q)]
        abel
  exact (key P hP).2

end SSAdm

end GlobalTheory.KZ
