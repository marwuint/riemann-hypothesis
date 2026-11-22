import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.TwoQ

section Gen

variable {F : Type} [Field F] {d β : F} {R T : Type} [CommRing R] [Algebra F R] [CommRing T]
  (ι : R →+* T) (h : T)

def th (x : Q d β R) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * h, ι (algebraMap F R β) * (ι x.imJ + ι x.imK * h);
     ι x.imJ - ι x.imK * h, ι x.re - ι x.imI * h]

variable {ι h}

theorem th_mul (hh : h * h = ι (algebraMap F R d)) (x y : Q d β R) :
    th ι h (x * y) = th ι h x * th ι h y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th, Matrix.mul_apply, Fin.sum_univ_two, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  · linear_combination (-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh
  · linear_combination (-ι (algebraMap F R β)) * (ι x.imI * ι y.imK - ι x.imK * ι y.imI) * hh
  · linear_combination (-(ι x.imI * ι y.imK - ι x.imK * ι y.imI)) * hh
  · linear_combination (-(ι x.imI * ι y.imI) + ι (algebraMap F R β) * ι x.imK * ι y.imK) * hh

theorem th_one : th ι h (1 : Q d β R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th]

theorem th_mul_star (hh : h * h = ι (algebraMap F R d)) {x : Q d β R} (hx : qn x = 1) :
    th ι h x * th ι h (star x) = 1 := by
  rw [← th_mul hh, mul_star_eq, hx, map_one, th_one]

theorem th_star_mul (hh : h * h = ι (algebraMap F R d)) {x : Q d β R} (hx : qn x = 1) :
    th ι h (star x) * th ι h x = 1 := by
  rw [← th_mul hh, star_mul_eq, hx, map_one, th_one]

theorem th_unitary (hh : h * h = ι (algebraMap F R d)) (c : T →+* T) (hc : ∀ a, c (ι a) = ι a) (hch : c h = -h)
    {x : Q d β R} (hx : qn x = 1) :
    Formalism.UG.cT c (th ι h x) * !![1, 0; 0, -ι (algebraMap F R β)] * th ι h x =
      !![1, 0; 0, -ι (algebraMap F R β)] := by
  have hq : ι x.re ^ 2 - ι (algebraMap F R d) * ι x.imI ^ 2 - ι (algebraMap F R β) * ι x.imJ ^ 2 +
      ι (algebraMap F R d) * ι (algebraMap F R β) * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simpa [qn] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th, Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, hc, hch]
  · linear_combination hq + (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh
  · ring
  · ring
  · linear_combination (-ι (algebraMap F R β)) * hq +
      (-ι (algebraMap F R β)) * (-(ι x.imI) ^ 2 + ι (algebraMap F R β) * ι x.imK ^ 2) * hh

end Gen

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d β : F} {R : Type} [CommRing R] [Algebra F R]

theorem incl_alg (t : F) :
    inclR R (algebraMap F E t) = algebraMap R (R ⊗[F] E) (algebraMap F R t) := by
  simp only [inclR]
  rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E) t]
  exact Algebra.TensorProduct.includeRight.commutes t

theorem xh_sq {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) :
    inclR (F := F) R ξ * inclR (F := F) R ξ = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  rw [← map_mul, ← pow_two, hξ, incl_alg]

theorem sig_alg (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_xh {σ : E →ₐ[F] E} {ξ : E} (hσ : σ ξ = -ξ) :
    sigR R σ (inclR (F := F) R ξ) = -inclR (F := F) R ξ := by
  simp [sigR, inclR, hσ, TensorProduct.tmul_neg]

theorem hermitian_plane_matrix :
    JR R (J2 E β) = !![1, 0; 0, -algebraMap R (R ⊗[F] E) (algebraMap F R β)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [JR, J2, incl_alg]

abbrev thR (R : Type) [CommRing R] [Algebra F R] (E : Type) [Field E] [Algebra F E] (ξ : E) (x : Q d β R) :
    Matrix (Fin 2) (Fin 2) (R ⊗[F] E) :=
  th (algebraMap R (R ⊗[F] E)) (inclR (F := F) R ξ) x

def toHA (σ : E →ₐ[F] E) {ξ : E} (hξ : ξ ^ 2 = algebraMap F E d) (hσ : σ ξ = -ξ) (x : Q d β R) (hx : qn x = 1) :
    HA R σ (J2 E β) :=
  (⟨⟨thR R E ξ x, thR R E ξ (star x), th_mul_star (xh_sq hξ) hx, th_star_mul (xh_sq hξ) hx⟩, by
    change Formalism.UG.cT (sigR R σ) (thR R E ξ x) * JR R (J2 E β) * thR R E ξ x = JR R (J2 E β)
    rw [hermitian_plane_matrix]
    exact th_unitary (xh_sq hξ) _ (sig_alg σ) (sig_xh hσ) hx⟩ : HR R σ (J2 E β))

end Tens

end GlobalTheory.CompanionTheory.PlaneSA.TwoQ
