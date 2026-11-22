import Development.WeilBound.CoreStatements.ThetaDilations.ParAlg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem exists_anti (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hss : ∀ x, σ (σ x) = x := GlobalTheory.GaussMean.OneVec.sigma_sigma h
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have h2 : σ y = y := by
    by_contra h3
    exact hne (y - σ y) (sub_ne_zero.2 (Ne.symm h3)) (by rw [map_sub, hss, neg_sub])
  have := h.2.2.2 τ y
  rw [h2] at this
  simpa using this.symm

theorem norm_sigR (h : IsCMExt F E σ) (a : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.norm R a) = a * sigR R σ a := by
  have ht : a + sigR R σ a = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) a) :=
    GlobalTheory.GaussMean.OneVec.add_sigR R h a
  let B := Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h.2.2.1)
  have key : algebraMap R (R ⊗[F] E) (Algebra.norm R a) =
      algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) a) * a - a * a := by
    apply Algebra.leftMulMatrix_injective B
    rw [map_sub, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.norm_eq_matrix_det B,
      Algebra.trace_eq_matrix_trace B]
    generalize Algebra.leftMulMatrix B a = A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply] <;> ring
  rw [key, ← ht]; ring

theorem cT_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

theorem hform_conj {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J : Matrix (Fin M) (Fin M) K} (hs : ∀ x, s (s x) = x)
    (hJ : cT s J = J) (x y : Fin M → K) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hform_add {K : Type} [CommRing K] {M : ℕ} (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J (x + y) (x + y) = hform s J x x + hform s J x y + hform s J y x + hform s J y y := by
  have e : (s : K → K) ∘ (x + y) = s ∘ x + s ∘ y := funext fun _ => map_add s _ _
  simp only [hform_eq, e, Matrix.add_vecMul, add_dotProduct, dotProduct_add]; ring

theorem hform_U {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J)
    (x : Fin M → K) : hform s J (U *ᵥ x) (U *ᵥ x) = hform s J x x := by
  have e : (s : K → K) ∘ (U *ᵥ x) = (s ∘ x) ᵥ* cT s U := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hU]

theorem hyp_inv {K : Type} [CommRing K] {M : ℕ} {J Ji : Matrix (Fin M) (Fin M) K} (h : Ji * J = 1) :
    hypJ Ji * hypJ J = 1 := by
  rw [← pm_one]
  simp [hypJ_eq, blk_mul, pm, h]

theorem continuous_pm {X K : Type} [TopologicalSpace X] [CommRing K] [TopologicalSpace K] {M : ℕ} {a b d : X → K}
    {r w : X → Fin M → K} {U : X → Matrix (Fin M) (Fin M) K} (ha : Continuous a) (hb : Continuous b)
    (hr : Continuous r) (hd : Continuous d) (hw : Continuous w) (hU : Continuous U) :
    Continuous fun x => pm (a x) (b x) (r x) (d x) (w x) (U x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  exacts [ha, hb, (continuous_apply j).comp hr, continuous_const, hd, continuous_const, continuous_const,
    (continuous_apply i).comp hw, hU.matrix_elem i j]

end PositivityTheory.PlacePermOperatorBicommutantSpan
