import Mathlib

noncomputable section

namespace PI.UMultOne.GelfSpanWork

open Matrix Module

variable {G : Type} [Group G] {N : ℕ}

def repEnd (ρ : G →* GL (Fin N) ℂ) : G →* Module.End ℂ (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  map_one' := by simp; rfl
  map_mul' x y := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

def spanAlg (ρ : G →* GL (Fin N) ℂ) : Subalgebra ℂ (Module.End ℂ (Fin N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (repEnd ρ))

instance spanAlg_tower (ρ : G →* GL (Fin N) ℂ) : IsScalarTower ℂ (spanAlg ρ) (Fin N → ℂ) :=
  ⟨fun _ _ _ => rfl⟩

theorem spanAlg_smul (ρ : G →* GL (Fin N) ℂ) (a : spanAlg ρ) (v : Fin N → ℂ) :
    a • v = (a : Module.End ℂ (Fin N → ℂ)) v := rfl

end PI.UMultOne.GelfSpanWork
