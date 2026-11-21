import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indScal_lift_law (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    (fun x => f x ⊗ₜ[ℂ] (1:ℂ)) ∈ indSpace (parab k (blocks a b))
      ((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) := by
  intro p x
  have h := hf.2 p x
  apply (TensorProduct.lid ℂ ℂ).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe] at h ⊢
  rw [h]
  simp [parChar, detRep, ofChar_apply]
  ring

def indScalLift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  ⟨⟨fun x => f x ⊗ₜ[ℂ] (1:ℂ), indScal_lift_law ν β a b hf⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((show IsOpen {g : GL (Fin (a + b)) k | rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f} from hf.1).mem_nhds (by simp)) fun g hg => by
      have hg' : rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f := hg
      apply Subtype.ext
      funext x
      show f (x * g) ⊗ₜ[ℂ] (1:ℂ) = f x ⊗ₜ[ℂ] (1:ℂ)
      rw [show f (x * g) = f x from congrFun hg' x])⟩

theorem indScal_lift_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b)
    (x : GL (Fin (a + b)) k) : TensorProduct.lid ℂ ℂ ((indScalLift ν β a b hf).1.1 x) = f x := by
  simp [indScalLift]

def indScalVal (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] (GL (Fin (a + b)) k → ℂ) where
  toFun F x := TensorProduct.lid ℂ ℂ (F.1.1 x)
  map_add' F G := by
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 x + G.1.1 x) = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext x
    show TensorProduct.lid ℂ ℂ (c • F.1.1 x) = _
    rw [map_smul]
    rfl

theorem indScal_scal_lift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    indScalVal ν β a b (indScalLift ν β a b hf) = f :=
  funext (indScal_lift_apply ν β a b hf)

end GlobalTheory.RankFibre
