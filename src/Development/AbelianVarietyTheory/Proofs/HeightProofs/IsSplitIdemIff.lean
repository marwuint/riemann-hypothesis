import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_mul_inv (V : HSp D) : HeisenbergWeilMatrices.gramA V * HeisenbergWeilMatrices.gramInvA V = 1 := by
  unfold HeisenbergWeilMatrices.gramA HeisenbergWeilMatrices.gramInvA
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inv_mul_gram (V : HSp D) : HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V = 1 := mul_eq_one_comm.1 (gram_mul_inv V)

def kap (A B : HSp D) : WA A B ≃+ WA A B where
  toFun x := HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x
  invFun y := HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ y
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, inv_mul_gram, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, gram_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem kap_apply (A B : HSp D) (x : WA A B) : kap A B x = HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x := rfl

theorem kap_symm_apply (A B : HSp D) (x : WA A B) : (kap A B).symm x = HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ x := rfl

def kapT (A B : HSp D) : WA A B ≃+ WA B A := (kap A B).trans (Matrix.transposeAddEquiv _ _ _)

def IsChange {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (σ : GA D V × GA D W → GA D A × GA D B) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ x y, symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp x y) ∧
    (∀ x, κ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B) ∧ (∀ (c : AE D) x, κ (c • x) = c • κ x) ∧
    ∀ g h x, actHom V W g h (κ x) = κ (HeisenbergWeilMatrices.act (σ (g, h)) x)

theorem isDetRoot_iff (V : HSp D) (g : GA D V) (x : (AE D)ˣ) :
    IsDetRoot V g x ↔ HeisenbergWeilMatrices.IsRoot D x (HeisenbergWeilMatrices.detA V g) := by
  unfold HeisenbergWeilMatrices.IsRoot
  rw [mul_inv_eq_iff_eq_mul, Units.ext_iff]; rfl

end GlobalTheory.WeilTieCompare

end
