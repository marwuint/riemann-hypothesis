import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesPolynomialVectorsSmallPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryDualPairGlobalToLocalTensorTransfer

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  classical

  have join : ∀ t₁ t₂ : M₀ ⊗[ℂ] (⨂[ℂ] i, M i),
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ + t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
    rintro t₁ t₂ ⟨m₁, f₁, φ₁, rfl⟩ ⟨m₂, f₂, φ₂, rfl⟩
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r g =>
      refine ⟨1, fun _ => r • x, fun _ => g, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add]
      exact join _ _ h₁ h₂
  | add t₁ t₂ h₁ h₂ => exact join _ _ h₁ h₂

theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h

  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Bᵀ * M * B.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have hmap : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, hmap, h0, map_zero, mul_zero]

theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · have hc : Continuous fun z => χ z / χ' z := h.1.div' h'.1
    exact hc
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · exact div_one 1
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

end GlobalTheory.HoweGlobalPair

end
