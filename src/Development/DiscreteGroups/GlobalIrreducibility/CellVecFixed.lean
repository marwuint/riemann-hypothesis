import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.InCellMulRightIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {S : Subgroup (GL (Fin m) k)}

def cellVec (hS1 : KOne k (Fin m) ≤ S)
    (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1) :
    IndSp (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ)) :=
  ⟨⟨cellFun S, fun p g => by
      rw [cellFun_mul_left hS4]
      simp [dl]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (GlobalTheory.StepData.isOpen_KOne.mem_nhds (one_mem _)) fun x hx =>
      Subtype.ext (funext fun g => cellFun_mul_right hS4 (hS1 hx) g))⟩

variable (hS1 : KOne k (Fin m) ≤ S)
  (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)

theorem cellVec_apply (g : GL (Fin m) k) : (cellVec hS1 hS4).1.1 g = cellFun S g := rfl

end DiscreteGroups.sglob.DzType
