import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

section LG

variable {E}

def ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : Ideal (𝓞 (maximalRealSubfield E)) where
  carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show algebraMap _ E (a + b) * t ∈ L
    rw [map_add, add_mul]; exact L.add_mem ha hb
  smul_mem' := fun c a ha => by
    show algebraMap _ E (c • a) * t ∈ L
    rw [smul_eq_mul, map_mul, mul_assoc]; exact hL.1 c _ ha

theorem mem_ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (a : 𝓞 (maximalRealSubfield E)) :
    a ∈ ann hL t ↔ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L := Iff.rfl

end LG

end Formalism.FourierDecayAlt.P.S6x6

namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
