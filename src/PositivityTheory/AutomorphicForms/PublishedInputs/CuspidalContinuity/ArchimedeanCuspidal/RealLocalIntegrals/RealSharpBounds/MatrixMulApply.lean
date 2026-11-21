import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.B

def mulTwoByThree : M23 →ₗ[ℝ] M3 →ₗ[ℝ] M23 :=
  LinearMap.mk₂ ℝ (fun X M => Matrix.of.symm (Matrix.of X * Matrix.of M))
    (fun X Y M => by ext r c; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc])
    (fun X M N => by ext r c; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm])

def mulB : M23 →L[ℝ] M3 →L[ℝ] M23 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (M3 →ₗ[ℝ] M23) ≃ₗ[ℝ] (M3 →L[ℝ] M23)).toLinearMap ∘ₗ mulTwoByThree)

def mulThreeByThree : M3 →ₗ[ℝ] M3 →ₗ[ℝ] M3 :=
  LinearMap.mk₂ ℝ (fun X M => Matrix.of.symm (Matrix.of X * Matrix.of M))
    (fun X Y M => by ext r c; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc])
    (fun X M N => by ext r c; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm])

def mul3 : M3 →L[ℝ] M3 →L[ℝ] M3 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (M3 →ₗ[ℝ] M3) ≃ₗ[ℝ] (M3 →L[ℝ] M3)).toLinearMap ∘ₗ mulThreeByThree)

def minv (M : M3) : M3 := Matrix.of.symm (Matrix.of M)⁻¹

def ell (M : M3) (i j : Fin 3) : M3 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) i)).comp (mul3 (minv M)))

theorem ell_apply (M : M3) (i j : Fin 3) (m : M3) :
    ell M i j m = ((((Matrix.of M)⁻¹ * Matrix.of m) i j : ℝ) : ℂ) := rfl

def Th (h : M22) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Matrix.of h)⁻¹)

end Ad3.LR.B
