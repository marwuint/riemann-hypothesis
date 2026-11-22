import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by
  simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add, ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

end GlobalTheory.LeviTorus
