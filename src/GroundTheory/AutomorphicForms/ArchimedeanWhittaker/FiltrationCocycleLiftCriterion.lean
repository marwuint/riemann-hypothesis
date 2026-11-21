import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Frechet
import GroundTheory.AutomorphicForms.HarishChandraRegularity
import GroundTheory.AutomorphicForms.RealGroupsKAK

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

abbrev FiltrationCocycleLiftCriterion : Subgroup (GL (Fin 2) ℝ) := ⊤

abbrev gl2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) := ⊤

theorem hGL2 : IsExpLieAlgebra FiltrationCocycleLiftCriterion gl2 := isExpLieAlgebra_top

noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) : FiltrationCocycleLiftCriterion :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, Subgroup.mem_top _⟩

@[simp] theorem coe_toGL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) :
    (((toGL A hA : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A := rfl

theorem GL2_ext {g g' : FiltrationCocycleLiftCriterion}
    (h : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ((g' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
    g = g' := Subtype.ext (Units.ext h)

noncomputable def nMat (x : ℝ) : FiltrationCocycleLiftCriterion := toGL !![1, x; 0, 1] (by simp)

noncomputable def kMat (θ : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    simp [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ])

noncomputable def aT (t : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.exp t, 0; 0, Real.exp (-t)] (by
    simp [Matrix.det_fin_two_of, ← Real.exp_add])

noncomputable def zPos (s : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.exp s, 0; 0, Real.exp s] (by
    simp [Matrix.det_fin_two_of])

noncomputable def eps : FiltrationCocycleLiftCriterion := toGL !![1, 0; 0, -1] (by simp [Matrix.det_fin_two_of])

@[simp] theorem coe_nMat (x : ℝ) :
    (((nMat x : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := rfl
@[simp] theorem coe_kMat (θ : ℝ) : (((kMat θ : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl
@[simp] theorem coe_aT (t : ℝ) : (((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.exp t, 0; 0, Real.exp (-t)] := rfl
@[simp] theorem coe_zPos (s : ℝ) : (((zPos s : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.exp s, 0; 0, Real.exp s] := rfl
@[simp] theorem coe_eps : (((eps : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![1, 0; 0, -1] := rfl

theorem kMat_add (a b : ℝ) : kMat (a + b) = kMat a * kMat b := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_kMat]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem kMat_two_pi : kMat (2 * Real.pi) = 1 := by
  apply GL2_ext; simp only [coe_kMat, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def lE : gl2 := ⟨!![0, 1; 0, 0], Submodule.mem_top⟩

def lF : gl2 := ⟨!![0, 0; 1, 0], Submodule.mem_top⟩

def lH : gl2 := ⟨!![1, 0; 0, -1], Submodule.mem_top⟩

def lW : gl2 := ⟨!![0, 1; -1, 0], Submodule.mem_top⟩

@[simp] theorem coe_lE : ((lE : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 0, 0] := rfl
@[simp] theorem coe_lF : ((lF : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 0; 1, 0] := rfl
@[simp] theorem coe_lH : ((lH : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, -1] := rfl
@[simp] theorem coe_lW : ((lW : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; -1, 0] := rfl

theorem exp_eq_of_hasDerivAt {X : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ t, HasDerivAt c (X * c t) t) (h0 : c 0 = 1) (t : ℝ) : exp (t • X) = c t := by
  have hcomm : ∀ s : ℝ, exp (s • X) * X = X * exp (s • X) := fun s =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).unique (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s)
  set D : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => exp ((-s) • X) * c s with hD
  have hDd : ∀ s, HasDerivAt D 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => exp ((-s) • X)) ((-1 : ℝ) • (X * exp ((-s) • X))) s :=
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-s)).scomp s (hasDerivAt_neg s)
    have h2 := h1.mul (hc s)
    refine h2.congr_deriv ?_
    rw [neg_one_smul, neg_mul, ← mul_assoc, hcomm, mul_assoc, neg_add_cancel]
  have hconst : D t = D 0 := is_const_of_deriv_eq_zero
    (fun s => (hDd s).differentiableAt) (fun s => (hDd s).deriv) t 0
  have hD0 : D 0 = 1 := by simp [hD, h0]
  have hinv : exp (t • X) * exp ((-t) • X) = 1 := by
    rw [← exp_add_of_commute' ℝ ((Commute.refl X).smul_left t |>.smul_right (-t)), ← add_smul,
      add_neg_cancel, zero_smul, exp_zero]
  calc exp (t • X) = exp (t • X) * D t := by rw [hconst, hD0, mul_one]
    _ = exp (t • X) * exp ((-t) • X) * c t := by simp [hD, mul_assoc]
    _ = c t := by rw [hinv, one_mul]

theorem expG_lW (θ : ℝ) : hGL2.expG (θ • lW) = kMat θ := by
  apply GL2_ext
  rw [IsExpLieAlgebra.coe_expG, coe_kMat, Submodule.coe_smul, coe_lW]
  have hc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Real.sin s • !![0, 1; -1, 0])
      (!![0, 1; -1, 0] * (Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin s • !![0, 1; -1, 0])) s := by
    intro s
    refine (((Real.hasDerivAt_cos s).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)).add
      ((Real.hasDerivAt_sin s).smul_const (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ))).congr_deriv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_of_hasDerivAt hc (by simp) θ]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def lS : gl2 := ⟨!![0, 1; 1, 0], Submodule.mem_top⟩

@[simp] theorem coe_lS : ((lS : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0] := rfl

theorem coe_Ad_GL2 (g : FiltrationCocycleLiftCriterion) (X : gl2) : ((hGL2.Ad g X : gl2) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * X *
      (((g⁻¹ : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker
