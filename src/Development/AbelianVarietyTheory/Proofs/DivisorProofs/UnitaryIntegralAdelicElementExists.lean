import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSConjGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OToSAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameMove

open Formalism.UG (bc cT)

theorem conj_gram {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (β G h : GL (Fin n) A) (hG : G.val = cT σ β.val * J * β.val)
    (hx : β * h * β⁻¹ ∈ Formalism.UG.UJ σ J) :
    (G * h * G⁻¹).val = cT σ (h⁻¹).val := by
  have hx' : cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val = J := hx
  have e1 : cT σ h.val * G.val * h.val = G.val := by
    have e : (β * h * β⁻¹).val * β.val = β.val * h.val := by
      rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    calc cT σ h.val * G.val * h.val = cT σ (β.val * h.val) * J * (β.val * h.val) := by
          rw [hG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ β.val * (cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val) * β.val := by
          rw [← e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G.val := by rw [hx', hG]
  have e2 : cT σ (h⁻¹).val * cT σ h.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc (G * h * G⁻¹).val = (cT σ (h⁻¹).val * cT σ h.val) * (G.val * h.val * (G⁻¹).val) := by
        rw [e2, Matrix.one_mul]; rfl
    _ = cT σ (h⁻¹).val * ((cT σ h.val * G.val * h.val) * (G⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = cT σ (h⁻¹).val := by rw [e1, Units.mul_inv, Matrix.mul_one]

theorem conj_gram_sub {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (O : Subring A) (J : Matrix (Fin n) (Fin n) A)
    (β : GL (Fin n) A) (G h : GL (Fin n) O) (hG : (bc O.subtype G).val = cT σ β.val * J * β.val)
    (hx : β * bc O.subtype h * β⁻¹ ∈ Formalism.UG.UJ σ J) (i j : Fin n) :
    (((G * h * G⁻¹).val i j : O) : A) = σ ((h⁻¹).val j i : O) := by
  have c := conj_gram σ J β (bc O.subtype G) (bc O.subtype h) hG hx
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul] at c
  exact congrFun (congrFun c i) j

end GlobalTheory.FrameMove
