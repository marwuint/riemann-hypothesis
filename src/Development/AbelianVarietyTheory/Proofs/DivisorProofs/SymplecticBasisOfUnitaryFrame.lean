import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTorus

open Module

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]

noncomputable def colTraceBil (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm F (Fin d → E) :=
  LinearMap.mk₂ F (fun f g => Algebra.trace F E (-1 * form σ K f g))
    (fun x x' y => by simp only [form, add_dotProduct, mul_add, map_add])
    (fun a x y => by simp only [form, smul_dotProduct, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.add_apply, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem colTraceBil_apply (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (f g : Fin d → E) :
    colTraceBil σ K f g = Algebra.trace F E (-1 * form σ K f g) := rfl

end

end GlobalTheory.ThKTorus
