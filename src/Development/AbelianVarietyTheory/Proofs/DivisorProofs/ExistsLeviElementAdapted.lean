import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def fm (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

def lev (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • Matrix.vecMulVec X (J *ᵥ fun i => c (Y i)) - (r - 1) • Matrix.vecMulVec Y (J *ᵥ fun i => c (X i))

theorem lev_mulVec (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) (w : Fin n → R) :
    lev c J X Y s r *ᵥ w = w + ((s - 1) * fm c J w Y) • X - ((r - 1) * fm c J w X) • Y := by
  ext i
  simp only [lev, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm w]
  ring

theorem fm_skew (hc : ∀ x, c (c x) = x) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = -J i j)
    (p q : Fin n → R) : fm c J p q = -c (fm c J q p) := by
  simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {c}

theorem fm_add_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u + u') v = fm c J u v + fm c J u' v := by
  simp [fm, add_dotProduct]

theorem fm_sub_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u - u') v = fm c J u v - fm c J u' v := by
  simp [fm, sub_dotProduct]

theorem fm_smul_left (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J (a • u) v = a * fm c J u v := by
  simp [fm, smul_dotProduct]

theorem entry (J M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Mᵀ * J * M.map c) i j = fm c J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [fm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
variable {R : Type} [CommRing R] {c : R →+* R} {n : ℕ}

section Plane
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
  (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1)
include hc hJ hxx hyy hxy

theorem fm_yx : fm c J Y X = -1 := by rw [fm_skew c hc J hJ, hxy, map_one]

theorem lev_mul (s r s' r' : R) : lev c J X Y s r * lev c J X Y s' r' = lev c J X Y (s * s') (r * r') := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have key : ∀ w, (lev c J X Y s r * lev c J X Y s' r') *ᵥ w = lev c J X Y (s * s') (r * r') *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, lev_mulVec, lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, hxx, hyy, hxy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem lev_one : lev c J X Y 1 1 = 1 := by simp [lev]

end Plane

theorem lev_X {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} (hxx : fm c J X X = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ X = s • X := by
  rw [lev_mulVec, hxx, hxy]; ext i; simp; ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, Algebra.TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

end GlobalTheory.LeviPlane
