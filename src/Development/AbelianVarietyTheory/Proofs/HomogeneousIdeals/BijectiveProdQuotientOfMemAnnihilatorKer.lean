import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftCoactionIffIsCoactionComm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv

namespace GlobalTheory

section Comodule

open CartierDual

variable {R C M M' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

def dualContraction (ρ : M →ₗ[R] M ⊗[R] C) : CartierDual R C →ₗ[R] Module.End R M :=
  (tensorToHom R M C ∘ₗ ρ).flip

theorem dualContraction_apply (ρ : M →ₗ[R] M ⊗[R] C) (w : CartierDual R C) (m : M) :
    dualContraction ρ w m = tensorToHom R M C (ρ m) w := rfl

theorem dualContraction_eq_rid (ρ : M →ₗ[R] M ⊗[R] C) (w : CartierDual R C) (m : M) :
    dualContraction ρ w m = TensorProduct.rid R M (w.ofConv.lTensor M (ρ m)) :=
  tensorToHom_apply _ _

variable (R M C) in

def dualContractionEquiv [Module.Finite R C] [Module.Projective R C] :
    (M →ₗ[R] M ⊗[R] C) ≃ (CartierDual R C →ₗ[R] Module.End R M) where
  toFun := dualContraction
  invFun θ := (tensorEquivHom R M C).symm.toLinearMap ∘ₗ θ.flip
  left_inv ρ := LinearMap.ext fun m => (tensorEquivHom R M C).symm_apply_apply (ρ m)
  right_inv θ := LinearMap.ext fun w => LinearMap.ext fun m =>
    congr($((tensorEquivHom R M C).apply_symm_apply (θ.flip m)) w)

@[simp] theorem dualContractionEquiv_apply [Module.Finite R C] [Module.Projective R C]
    (ρ : M →ₗ[R] M ⊗[R] C) : dualContractionEquiv R C M ρ = dualContraction ρ := rfl

variable [Coalgebra R C]

private theorem tensorToHom_assoc_rTensor (ρ : M →ₗ[R] M ⊗[R] C) (φ ψ : CartierDual R C)
    (x : M ⊗[R] C) :
    tensorToHom R M (C ⊗[R] C) (TensorProduct.assoc R M C C (ρ.rTensor C x))
      (toConv (pair R C C (φ ⊗ₜ ψ))) = dualContraction ρ φ (tensorToHom R M C x ψ) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul m c =>
    rw [LinearMap.rTensor_tmul, tensorToHom_tmul, map_smul, dualContraction_apply]
    generalize ρ m = s
    induction s with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, add_tmul, smul_add, hx, hy]
    | tmul m' c' => simp [smul_smul, mul_comm]

private theorem tensorToHom_lTensor_comul (φ ψ : CartierDual R C) (x : M ⊗[R] C) :
    tensorToHom R M (C ⊗[R] C) ((comul : C →ₗ[R] C ⊗[R] C).lTensor M x)
      (toConv (pair R C C (φ ⊗ₜ ψ))) = tensorToHom R M C x (φ * ψ) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul m c => rw [LinearMap.lTensor_tmul, tensorToHom_tmul, tensorToHom_tmul, mul_apply]

theorem IsCoaction.dualContraction_one {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    dualContraction ρ 1 = 1 :=
  LinearMap.ext fun m => (dualContraction_eq_rid ρ 1 m).trans (h.rid_counit m)

theorem IsCoaction.dualContraction_mul {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (φ ψ : CartierDual R C) :
    dualContraction ρ (φ * ψ) = dualContraction ρ φ * dualContraction ρ ψ :=
  LinearMap.ext fun m => by
    rw [Module.End.mul_apply, dualContraction_apply, dualContraction_apply ρ ψ,
      ← tensorToHom_lTensor_comul, ← h.coassoc, tensorToHom_assoc_rTensor]

theorem isCoaction_iff_dualContraction [Module.Finite R C] [Module.Projective R C]
    {ρ : M →ₗ[R] M ⊗[R] C} :
    IsCoaction ρ ↔ dualContraction ρ 1 = 1 ∧
      ∀ φ ψ, dualContraction ρ (φ * ψ) = dualContraction ρ φ * dualContraction ρ ψ := by
  refine ⟨fun h => ⟨h.dualContraction_one, h.dualContraction_mul⟩, fun ⟨h1, h2⟩ =>
    ⟨fun m => eq_of_forall_tensorToHom_pair fun φ ψ => ?_, fun m => ?_⟩⟩
  · rw [tensorToHom_lTensor_comul, tensorToHom_assoc_rTensor]
    exact congr($(h2 φ ψ) m).symm
  · refine (TensorProduct.rid R M).injective ?_
    rw [TensorProduct.rid_tmul, one_smul]
    exact (dualContraction_eq_rid ρ 1 m).symm.trans congr($h1 m)

def IsCoaction.dualAction {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    CartierDual R C →ₐ[R] Module.End R M :=
  AlgHom.ofLinearMap (dualContraction ρ) h.dualContraction_one h.dualContraction_mul

@[simp] theorem IsCoaction.dualAction_apply {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (w : CartierDual R C) : h.dualAction w = dualContraction ρ w := rfl

abbrev IsCoaction.dualModule {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    Module (CartierDual R C) M :=
  Module.compHom M h.dualAction.toRingHom

variable (R C M) in

def coactionEquivDualAction [Module.Finite R C] [Module.Projective R C] :
    {ρ : M →ₗ[R] M ⊗[R] C // IsCoaction ρ} ≃ (CartierDual R C →ₐ[R] Module.End R M) where
  toFun ρ := ρ.2.dualAction
  invFun θ := ⟨(dualContractionEquiv R C M).symm θ.toLinearMap, by
    rw [isCoaction_iff_dualContraction, ← dualContractionEquiv_apply, Equiv.apply_symm_apply]
    exact ⟨map_one θ, map_mul θ⟩⟩
  left_inv ρ := Subtype.ext ((dualContractionEquiv R C M).symm_apply_apply ρ.1)
  right_inv θ := AlgHom.toLinearMap_injective
    ((dualContractionEquiv R C M).apply_symm_apply θ.toLinearMap)

@[simp] theorem coactionEquivDualAction_apply [Module.Finite R C] [Module.Projective R C]
    (ρ : {ρ : M →ₗ[R] M ⊗[R] C // IsCoaction ρ}) :
    coactionEquivDualAction R C M ρ = ρ.2.dualAction := rfl

end Comodule

section Invariants

variable {R H M : Type*} [CommRing R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [AddCommGroup M] [Module R M]

end Invariants

section BaseChange

variable {R D : Type*} (K : Type*) [CommRing R] [CommRing D] [Algebra R D] [CommRing K]
  [Algebra R K]

def augmentationBaseChange (ε : D →ₐ[R] R) : K ⊗[R] D →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp ε) fun _ _ => Commute.all _ _

@[simp] theorem augmentationBaseChange_tmul (ε : D →ₐ[R] R) (k : K) (d : D) :
    augmentationBaseChange K ε (k ⊗ₜ d) = k * algebraMap R K (ε d) := rfl

variable {K}

end BaseChange

section Cramer

open Matrix

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

open MvPowerSeries

variable {R : Type*} [CommRing R]

variable {D : Type*} [CommRing D] [Algebra R D]

omit [Fintype σ] [DecidableEq σ] in

def quotientConstantCoeff {τ : Type*} (f : τ → MvPowerSeries σ R)
    (hf : ∀ i, constantCoeff (f i) = 0) :
    (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ { constantCoeff with commutes' := fun r => constantCoeff_C r }
    fun _ hg => (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i) :
      Ideal.span (Set.range f) ≤ germIdeal σ R) hg

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem quotientConstantCoeff_mk {τ : Type*} (f : τ → MvPowerSeries σ R)
    (hf : ∀ i, constantCoeff (f i) = 0) (g : MvPowerSeries σ R) :
    quotientConstantCoeff f hf (Ideal.Quotient.mk _ g) = constantCoeff g := rfl

end Cramer

universe u v w

end GlobalTheory
