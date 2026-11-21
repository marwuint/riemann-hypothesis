import Mathlib

namespace PI.UnitaryGroupMassFormula.ChiExCM

open NumberField

section

variable {E : Type} [Field E] [NumberField E]

noncomputable def spanHom : E →* Submodule (𝓞 E) E where
  toFun x := Submodule.span (𝓞 E) {x}
  map_one' := Submodule.one_eq_span.symm
  map_mul' x y := by
    show Submodule.span (𝓞 E) {x * y} = Submodule.span (𝓞 E) {x} * Submodule.span (𝓞 E) {y}
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

def normOne (c : E →+* E) : Subgroup Eˣ where
  carrier := {u | (u : E) * c u = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at *
    calc (a : E) * b * (c a * c b) = ((a : E) * c a) * ((b : E) * c b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
    rw [← mul_inv, ha, inv_one]

theorem mem_normOne (c : E →+* E) (u : Eˣ) : u ∈ normOne c ↔ (u : E) * c u = 1 := Iff.rfl

noncomputable def iota (c : E →+* E) : normOne c →* (Submodule (𝓞 E) E)ˣ :=
  (Units.map spanHom).comp (normOne c).subtype

theorem iota_val (c : E →+* E) (u : normOne c) :
    ((iota c u : (Submodule (𝓞 E) E)ˣ) : Submodule (𝓞 E) E) = Submodule.span (𝓞 E) {((u : Eˣ) : E)} := rfl

end

end PI.UnitaryGroupMassFormula.ChiExCM
