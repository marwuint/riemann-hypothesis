import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicConverse

open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

variable (L₁ L₂) in

def latticeHomEquiv : latticeHom L₁ L₂ ≃+ isogHom (weierstrassCurve L₁) (weierstrassCurve L₂) where
  toFun := latticeToHom
  invFun Q := ⟨_, homConst_mem_latticeHom Q⟩
  left_inv α := Subtype.ext (homConst_latticeToHom α)
  right_inv Q := latticeToHom_homConst Q
  map_add' := latticeToHom_add

variable (L : PeriodPair)

def latticeEnd : Subring ℂ where
  carrier := {α | ∀ l ∈ L.lattice, α * l ∈ L.lattice}
  add_mem' ha hb := (latticeHom L L).add_mem ha hb
  zero_mem' := (latticeHom L L).zero_mem
  neg_mem' ha := (latticeHom L L).neg_mem ha
  one_mem' l hl := by rwa [one_mul]
  mul_mem' {a b} ha hb l hl := by
    rw [mul_assoc]
    exact ha _ (hb l hl)

def latticeEndEquiv : latticeEnd L ≃+* isogEnd (weierstrassCurve L) where
  toFun α := latticeToHom ⟨α, α.2⟩
  invFun Q := ⟨homConst (weierstrassCurve L) (weierstrassCurve L) Q, homConst_mem_latticeHom Q⟩
  left_inv _ := Subtype.ext (homConst_latticeToHom _)
  right_inv Q := latticeToHom_homConst Q
  map_mul' α β := latticeToHom_mul ⟨α, α.2⟩ ⟨β, β.2⟩ (α * β).2
  map_add' α β := latticeToHom_add ⟨α, α.2⟩ ⟨β, β.2⟩

theorem homConst_latticeEndEquiv (α : latticeEnd L) :
    homConst (weierstrassCurve L) (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeToHom _

variable {L}

def mulLattice (α : latticeHom L₁ L₂) : AddSubgroup L₂.lattice where
  carrier := {w | ∃ l ∈ L₁.lattice, (w : ℂ) = α * l}
  add_mem' := by
    rintro a b ⟨l, hl, ha⟩ ⟨l', hl', hb⟩
    exact ⟨l + l', add_mem hl hl', by rw [Submodule.coe_add, ha, hb, mul_add]⟩
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    rintro a ⟨l, hl, ha⟩
    exact ⟨-l, neg_mem hl, by rw [Submodule.coe_neg, ha, mul_neg]⟩

theorem mem_mulLattice {α : latticeHom L₁ L₂} {w : L₂.lattice} :
    w ∈ mulLattice α ↔ ∃ l ∈ L₁.lattice, (w : ℂ) = α * l :=
  Iff.rfl

end Elliptic
end GroundTheory.Global
