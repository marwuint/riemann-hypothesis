import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlueA

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsKCRT

open NumberField Matrix IsDedekindDomain Formalism.MainNotions.S Formalism.L2.SG.Pf.unitaryCongruence
open scoped TensorProduct

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def pm (u : R) (X : Matrix n n R) : Matrix n n R := 1 + u • (X - 1)

theorem pm_one (u : R) : pm u (1 : Matrix n n R) = 1 := by simp [pm]

theorem one_add_mul_one_add (a b : Matrix n n R) : (1 + a) * (1 + b) = 1 + a + b + a * b := by noncomm_ring

theorem pm_mul {u : R} (hu : u * u = u) (X Y : Matrix n n R) : pm u X * pm u Y = pm u (X * Y) := by
  have e : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  unfold pm
  rw [one_add_mul_one_add, smul_mul_smul_comm, hu, e, smul_add, smul_add]
  abel

theorem cT_pm (σ : R →+* R) {u : R} (hu : σ u = u) (X : Matrix n n R) :
    Formalism.UG.cT σ (pm u X) = pm u (Formalism.UG.cT σ X) := by
  ext a b
  simp only [Formalism.UG.cT, pm, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hu, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

theorem pm_form {u : R} (hu : u * u = u) (A J X : Matrix n n R) (h : A * J * X = J) :
    pm u A * J * pm u X = J := by
  have e : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = A * J * X - J := by noncomm_ring
  have e0 : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = 0 := by rw [e, h, sub_self]
  have key : (A - 1) * J * (X - 1) = -((A - 1) * J + J * (X - 1)) := eq_neg_of_add_eq_zero_right e0
  have e3 : ∀ a b : Matrix n n R, (1 + a) * J * (1 + b) = J + a * J + J * b + a * J * b := by
    intro a b; noncomm_ring
  unfold pm
  rw [e3, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, hu, key, smul_neg, smul_add]
  abel

end Alg

section Inst

variable (I : AutInst)

open LatDictZ.Z5

theorem fmat_mul_inv' (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  rw [← fmat_mul, mul_inv_cancel, fmat_one]

def mkG (u : I.E ⊗[I.F] Af I.F) (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u) (x : I.Gf) : I.Gf :=
  ⟨⟨pm u (I.fmat x), pm u (I.fmat x⁻¹),
    by rw [pm_mul hu, fmat_mul_inv', pm_one], by rw [pm_mul hu, fmat_inv_mul, pm_one]⟩, by
    have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (pm u (I.fmat x)) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        pm u (I.fmat x) = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [cT_pm _ hσ]
    exact pm_form hu _ _ _ hx⟩

theorem fmat_mkG (u : I.E ⊗[I.F] Af I.F) (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u) (x : I.Gf) :
    I.fmat (mkG I u hu hσ x) = pm u (I.fmat x) := rfl

end Inst

end Formalism.L2.SG.Pf.AllRowsKCRT
