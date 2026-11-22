import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchTraceNondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro hM
  apply h2
  simp [Matrix.det_mul, hM]

theorem det_J_ne_zero {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem sigma_surjective (σ : E →ₐ[F] E) : Function.Surjective σ := by
  have hinj : Function.Injective ((σ : E →+* E).toRatAlgHom.toLinearMap) := (σ : E →+* E).injective
  exact LinearMap.injective_iff_surjective.1 hinj

def cAinv (σ : E →ₐ[F] E) : AE F E →ₐ[AF F] AE F E :=
  Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F))
    (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩).symm.toAlgHom

theorem cA_cAinv (σ : E →ₐ[F] E) (x : AE F E) : cA σ (cAinv σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [cAinv, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact AlgEquiv.apply_symm_apply (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩) y
  | add x y hx hy => simp only [map_add, hx, hy]

theorem at_single {n : ℕ} (k : Fin n) {t : AE F E} (ht : At (evI F) t) :
    At (evI F) (Pi.single k t : Fin n → AE F E) := by
  intro u hu
  funext j
  by_cases hj : j = k
  · subst hj; simp [ht u hu]
  · simp [Pi.single_apply, hj]

end GlobalTheory.ArchTraceNondeg
