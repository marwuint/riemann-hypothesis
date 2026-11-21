import Mathlib
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.WmSysObjects
import GroundTheory.GlobalFields.TateThesis.AdelicChar

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global NumberField MeasureTheory TensorProduct
open scoped NumberField.AdeleRing ComplexOrder

noncomputable section

section Alg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

variable {P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]

namespace FourPieces

variable {ω : LinearMap.BilinForm R W}

def incP₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : P₂ →ₗ[R] W :=
  F.e.symm.toLinearMap ∘ₗ LinearMap.inl R (P₁ × P₂) (Q₁ × Q₂) ∘ₗ LinearMap.inr R P₁ P₂

def incQ₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : Q₂ →ₗ[R] W :=
  F.e.symm.toLinearMap ∘ₗ LinearMap.inr R (P₁ × P₂) (Q₁ × Q₂) ∘ₗ LinearMap.inr R Q₁ Q₂

theorem incP₂_apply (F : FourPieces ω P₁ P₂ Q₁ Q₂) (p : P₂) :
    F.incP₂ p = F.e.symm ((0, p), (0, 0)) := rfl

theorem incQ₂_apply (F : FourPieces ω P₁ P₂ Q₁ Q₂) (q : Q₂) :
    F.incQ₂ q = F.e.symm ((0, 0), (0, q)) := rfl

end FourPieces

end Alg

namespace FourPieces

end FourPieces

section Inhabitants

variable (R : Type*) [CommRing R]

def lineFourForm : LinearMap.BilinForm R ((R × R) × (R × R)) :=
  LinearMap.mk₂ R
    (fun w w' ↦ w.1.1 * w'.2.1 + w.1.2 * w'.2.2 - w'.1.1 * w.2.1 - w'.1.2 * w.2.2)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ ↦ by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem lineFourForm_apply (w w' : (R × R) × (R × R)) :
    lineFourForm R w w' = w.1.1 * w'.2.1 + w.1.2 * w'.2.2 - w'.1.1 * w.2.1 - w'.1.2 * w.2.2 := rfl

end Inhabitants

end

end GroundTheory.Heights₂.Theta
