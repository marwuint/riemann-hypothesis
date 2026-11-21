import Formalism.LocalRingCardinality.PosOfIsomEmb
import Mathlib

noncomputable section

open NumberField Matrix
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

structure Model (S : HSpace E) where
  Y : (E →+* ℂ) → Matrix (Fin S.rank) (Fin S.rank) ℂ
  hY : ∀ σ (y : S.V), ∑ i, ‖(Y σ *ᵥ fun j ↦ σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re

abbrev Idx (S : HSpace E) := (E →+* ℂ) × Fin S.rank × Bool

def vec {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (x : S.V) : Fin S.rank → ℂ :=
  M.Y σ *ᵥ fun j ↦ σ (S.frame.repr x j)

theorem vec_add {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (x y : S.V) :
    vec M σ (x + y) = vec M σ x + vec M σ y := by
  unfold vec
  rw [← Matrix.mulVec_add]
  congr 1
  ext j
  simp

def psi {S : HSpace E} (M : Model S) : S.V →+ EuclideanSpace ℝ (Idx S) where
  toFun x := WithLp.toLp 2 fun p ↦ if p.2.2 then (vec M p.1 x p.2.1).re else (vec M p.1 x p.2.1).im
  map_zero' := by
    ext p
    simp only [vec, map_zero, LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have h0 : (fun _ : Fin S.rank ↦ (0 : ℂ)) = 0 := rfl
    rw [h0, Matrix.mulVec_zero]
    split_ifs <;> simp
  map_add' x y := by
    ext p
    simp only [vec_add, Pi.add_apply, Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> rfl

theorem psi_apply {S : HSpace E} (M : Model S) (x : S.V) (p : Idx S) :
    psi M x p = if p.2.2 then (vec M p.1 x p.2.1).re else (vec M p.1 x p.2.1).im := rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
