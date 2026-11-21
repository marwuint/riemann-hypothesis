import Mathlib

open scoped TensorProduct

namespace UpperTheory.Reformulated.B.Qk3

theorem aux1 {A : Type} [inst : CommRing A] :
    RingHomInvPair (RingHom.id A) (RingHom.id A) :=
  RingHomInvPair.ids

noncomputable def unopS (A E S : Type) [inst : CommRing A] [inst_1 : Ring E]
    [inst_2 : Algebra A E] [inst_3 : CommRing S] [inst_4 : Algebra A S] :
    (S ⊗[A] Eᵐᵒᵖ) →ₗ[S] (S ⊗[A] E) :=
  let invPair := @aux1 A inst
  LinearMap.baseChange S <|
    @LinearEquiv.toLinearMap A A _ _ _ _ invPair invPair Eᵐᵒᵖ E _ _ _ _ <|
      @LinearEquiv.symm A A E Eᵐᵒᵖ _ _ _ _ _ _ _ _ invPair invPair
        (MulOpposite.opLinearEquiv A (M := E))

theorem unopS_mul {A E : Type} [inst : CommRing A] [inst_1 : Ring E]
    [inst_2 : Algebra A E] (S : Type) [inst_3 : CommRing S] [inst_4 : Algebra A S]
    (x y : S ⊗[A] Eᵐᵒᵖ) :
    unopS A E S (x * y) = unopS A E S y * unopS A E S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, mul_add]
  | tmul s e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, add_mul]
    | tmul t f =>
      simp [unopS, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s t]

end UpperTheory.Reformulated.B.Qk3
