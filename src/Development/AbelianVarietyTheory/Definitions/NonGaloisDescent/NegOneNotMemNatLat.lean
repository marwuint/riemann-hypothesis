import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def eLast (R : Type*) [CommRing R] (a : ℕ) : Fin a → R := fun i => if (i : ℕ) + 1 = a then 1 else 0

theorem secRow_eLast {R : Type*} [CommRing R] : secRow (eLast R a) = 1 := by
  ext i j
  simp only [secRow, eLast, Matrix.of_apply, Matrix.one_apply]
  by_cases h : (i : ℕ) + 1 = a
  · rw [if_pos h]
    by_cases h2 : (j : ℕ) + 1 = a
    · rw [if_pos h2, if_pos (Fin.ext (by omega))]
    · rw [if_neg h2, if_neg (fun e : i = j => h2 (e ▸ h))]
  · rw [if_neg h]

omit [NumberField E] [IsTotallyComplex E] in
theorem secInv_eLast : secInv (eLast (Cinf E) a) = 1 := by
  unfold secInv
  split_ifs with h
  · rw [inv_eq_one]; exact Units.ext secRow_eLast
  · rfl

omit [IsTotallyComplex E] in
theorem detPow_mul (x : ℝ) (g h : GA E a) : detPow E a x (g * h) = detPow E a x g * detPow E a x h := by
  simp [detPow]

omit [IsTotallyComplex E] in

theorem detPow_ratGL (x : ℝ) (γ : GL (Fin a) E) : detPow E a x (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = diagUnits E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map (algebraMap E (Ad E)) γ)
  have h2 := (GlobalTheory.HeckeGal.Model.absPow E x).2.2 (Matrix.GeneralLinearGroup.det γ)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, h, h2]; simp

end GlobalTheory.RSJ.Model
