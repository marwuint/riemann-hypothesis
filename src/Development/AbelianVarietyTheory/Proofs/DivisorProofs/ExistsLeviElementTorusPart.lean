import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

theorem fR_smul_left (r : R) (u v : Fin n → R) : fR c J (r • u) v = r * fR c J u v := by
  simp [fR, smul_dotProduct]

theorem fR_mulVec (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    fR c J (A *ᵥ u) (A *ᵥ v) = u ⬝ᵥ (Aᵀ * J * A.map c) *ᵥ (fun i => c (v i)) := by
  have h : (fun i => c ((A *ᵥ v) i)) = A.map c *ᵥ fun i => c (v i) := by
    funext i; exact RingHom.map_mulVec c A v i
  simp only [fR, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Aᵀ, Matrix.vecMul_transpose]

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem fR_inc (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    fR (cA σ).toRingHom (incM F J) (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  simp [fR, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_incl]

end Main

end GlobalTheory.AdelicPlaneLevi

end
