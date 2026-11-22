import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem mem_unipRad_iff_dual {C D : Matrix (Fin n) (Fin r) E} (xy : cT (σ : E →+* E) C * J * D = 1) (g : GAd σ J) :
    g ∈ unipRad σ J C ↔ ((matHom _ σ J g).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin r) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J g).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
  constructor
  · intro hg
    simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
      sub_eq_iff_eq_add, zero_add]
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, -, h3⟩ := hg
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, xy, Matrix.mul_one, Matrix.one_mul, sub_self]
      choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
        (funext fun j => congrFun (congrFun hT j) k)
      refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
      rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
      ext i k
      exact congrFun (ha k) i
    | one => exact ⟨by simp, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a1, A, a2⟩ := ha
      obtain ⟨b1, B, b2⟩ := hb
      refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
        add_assoc]
    | inv a _ ha =>
      obtain ⟨a1, A, a2⟩ := ha
      have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
        conv_lhs => rw [← a1]
        rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      refine ⟨i1, -A, ?_⟩
      have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
      rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
      rw [Matrix.mul_neg]
      conv_rhs => rw [this]
      abel
  · rintro ⟨h1, B, h2⟩
    refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
    · have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
      have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
      conv_lhs => rw [← h1, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J g).1)]
      exact congrArg _ hg
    · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
          fun i => inclR (F := F) (AF F) (x i) := by
        funext i
        have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
        exact this.symm
      rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]

end GlobalTheory.EisCT

end
