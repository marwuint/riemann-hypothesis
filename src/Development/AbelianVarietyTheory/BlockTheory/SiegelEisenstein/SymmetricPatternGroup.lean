import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Pattern
variable {F : Type*} [Field F] [Finite F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mul_apply_of_no_path {A : ι → ι → Prop} {g h : Matrix ι ι F}
    (hg : ∀ r s, ¬ A r s → g r s = (1 : Matrix ι ι F) r s) (hh : ∀ r s, ¬ A r s → h r s = (1 : Matrix ι ι F) r s)
    (hi : ∀ r, ¬ A r r) {r s : ι} (hp : ∀ l, A r l → ¬ A l s) :
    (g * h) r s = g r s + h r s - (1 : Matrix ι ι F) r s := by
  have e : g * h = (g - 1) * (h - 1) + g + h - 1 := by noncomm_ring
  have z : ((g - 1) * (h - 1)) r s = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : A r l
    · simp [hh l s (hp l h1)]
    · simp [hg r l h1]
  rw [e]; simp [z]

variable (F) in

def patGrp (A : ι → ι → Prop) (hi : ∀ r, ¬ A r r) (ht : ∀ r l s, A r l → A l s → A r s) : Subgroup (GL ι F) :=
  let M : Submonoid (GL ι F) :=
    { carrier := {g | ∀ r s, ¬ A r s → g.val r s = (1 : Matrix ι ι F) r s}
      one_mem' := fun _ _ _ => rfl
      mul_mem' := fun {g h} hg hh r s hrs => by
        rw [Units.val_mul, mul_apply_of_no_path hg hh hi fun l h1 h2 => hrs (ht _ _ _ h1 h2), hg r s hrs, hh r s hrs,
          add_sub_cancel_right] }
  { M with
    inv_mem' := fun {g} hg => by
      have h0 : 0 < orderOf g := orderOf_pos g
      have e : g⁻¹ = g ^ (orderOf g - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
      rw [e]; exact M.pow_mem hg _ }

theorem mem_patGrp {A : ι → ι → Prop} {hi ht} {g : GL ι F} :
    g ∈ patGrp F A hi ht ↔ ∀ r s, ¬ A r s → g.val r s = (1 : Matrix ι ι F) r s := Iff.rfl

end Pattern

end GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
