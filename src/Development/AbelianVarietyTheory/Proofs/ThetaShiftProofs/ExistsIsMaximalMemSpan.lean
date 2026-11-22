import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsLZBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegerRingSmulMemSubmodule

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.TorusFourier
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsotropicSub (G : Matrix (Fin r) (Fin r) E) (V : Submodule E (Fin r → E)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, herm G v w = 0

theorem isIsotropicSub_span {G : Matrix (Fin r) (Fin r) E} {s : Set (Fin r → E)}
    (h : ∀ v ∈ s, ∀ w ∈ s, herm G v w = 0) : IsIsotropicSub G (Submodule.span E s) := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [herm, cc]
    | add y z _ _ hy hz =>
      have : herm G x (y + z) = herm G x y + herm G x z := by
        simp [herm, cc, mul_add, Finset.sum_add_distrib]
      rw [this, hy, hz, add_zero]
    | smul c y _ hy =>
      have : herm G x (c • y) = cc c * herm G x y := by
        simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hy, mul_zero]
  | zero => simp [herm]
  | add x y _ _ hx hy =>
    have : herm G (x + y) w = herm G x w + herm G y w := by
      simp [herm, add_mul, Finset.sum_add_distrib]
    rw [this, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_left', hx, mul_zero]

theorem exists_smul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ X.Λ := by
  first
  | exact @_root_.GlobalTheory.SubmoduleScalarClosure.main
  | exact _root_.GlobalTheory.SubmoduleScalarClosure.main
  | (apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubmoduleScalarClosure.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubmoduleScalarClosure.main ..)

section Torus

variable (X : Data E r)

end Torus

end

end GlobalTheory.MaxCusp
