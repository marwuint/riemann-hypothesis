import Mathlib
import GroundTheory.LocalFields.BrauerInductionCharacters
import GroundTheory.LocalFields.BrauerInductionInduced

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Basics

variable {G : Type*} [Group G]

def linRep (l : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := (l g : ℂ) • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_comm]

theorem linRep_apply (l : G →* ℂˣ) (g : G) (z : ℂ) : linRep l g z = (l g : ℂ) * z := rfl

instance linRep_isIrreducible (l : G →* ℂˣ) : (linRep l).IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, fun h ↦
    (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩
  eq_bot_or_eq_top U := by
    rcases Ideal.eq_bot_or_top U.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

variable [Fintype G]

end Basics

section Conj

variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]

def conjNormal (g : G) : A ≃* A where
  toFun a := ⟨g⁻¹ * a * g, by simpa using hA.conj_mem a a.2 g⁻¹⟩
  invFun a := ⟨g * a * g⁻¹, hA.conj_mem a a.2 g⟩
  left_inv a := by
    ext
    simp [mul_assoc]
  right_inv a := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

@[simp]
theorem coe_conjNormal (g : G) (a : A) : (conjNormal A g a : G) = g⁻¹ * a * g := rfl

end Conj

end GroundTheory.LocalField
