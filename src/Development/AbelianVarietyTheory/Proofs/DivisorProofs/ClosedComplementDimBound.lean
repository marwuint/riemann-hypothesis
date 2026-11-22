import Mathlib

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.DimCodim

section

attribute [local instance low] specializationOrder

theorem dim_add_le_of_le_coheight {S W : Type*} [TopologicalSpace S] [TopologicalSpace W]
    [QuasiSober S] [T0Space S] [QuasiSober W] [T0Space W] {j : W → S} (hj : Continuous j)
    (hi : Function.Injective j) (c : ℕ∞) (h : ∀ w, c ≤ Order.coheight (j w)) :
    topologicalKrullDim W + c ≤ topologicalKrullDim S := by
  have hmono : StrictMono j := by
    intro x y hxy
    refine lt_of_le_of_ne ?_ (fun hxy' => hxy.ne (hi hxy'))
    exact (show y ⤳ x from hxy.le).map hj
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [Order.krullDim_eq_bot]
    simp
  · have : Nonempty S := ⟨j hW.some⟩
    rw [Order.krullDim_eq_iSup_height_of_nonempty,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add,
      WithBot.coe_le_coe, ENat.iSup_add]
    refine iSup_le fun w => le_trans ?_
      (le_iSup (fun a : S => Order.height a + Order.coheight a) (j w))
    exact add_le_add (Order.height_le_height_apply_of_strictMono j hmono w) (h w)

end

end GlobalTheory.DimCodim
