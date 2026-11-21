import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDualNeZeroCompEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientSpanSingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthSelfEqTop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Imports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanEqAddValDet

open Module IsDiscreteValuationRing

namespace GlobalTheory

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section Cokernel

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  first
  | (rename_i h_1 h_2 h_3; revert R h_1 h_2 h_3 ι s a; exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod)
  | exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | (apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod ..)

theorem length_quotient_range_eq_top_of_det_eq_zero [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (hf : LinearMap.det f = 0) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 f hf; exact @_root_.GlobalTheory.LengthDualFunctional.main)
  | exact @_root_.GlobalTheory.LengthDualFunctional.main
  | exact _root_.GlobalTheory.LengthDualFunctional.main
  | (apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthDualFunctional.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthDualFunctional.main ..)

theorem length_quotient_eq_addVal_det_equiv [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) = addVal R (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 N e; exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det)
  | exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det ..)

theorem length_quotient_range_eq_addVal_det [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.det f = 0
  · rw [length_quotient_range_eq_top_of_det_eq_zero hf, hf, addVal_zero]
  · have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      by_contra h
      exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    exact length_quotient_eq_addVal_det_equiv _ (LinearEquiv.ofInjective f hinj)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem length_quotient_range_toLin'_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range (Matrix.toLin' P)) = addVal R P.det := by
  rw [length_quotient_range_eq_addVal_det, LinearMap.det_toLin']

theorem length_quotient_range_mulVecLin_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det :=
  length_quotient_range_toLin'_eq_addVal_det P

theorem length_quotient_range_eq_addVal_det_toMatrix {M' : Type*} [AddCommGroup M'] [Module R M']
    (b' : Basis ι R M') (b : Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.toMatrix b' b f).det := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9 h_11 h_12; revert R h_1 h_2 h_3 M h_5 h_6 ι h_8 h_9 M' h_11 h_12 b' b f; exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main)
  | exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main
  | exact _root_.GlobalTheory.LengthQuotientSpanValuation.main
  | (apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientSpanValuation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientSpanValuation.main ..)

theorem length_quotient_span_eq_addVal_det (b : Basis ι R M) (v : ι → M) :
    Module.length R (M ⧸ Submodule.span R (Set.range v)) = addVal R (b.det v) := by
  rw [← b.constr_range R, length_quotient_range_eq_addVal_det_toMatrix b b, Basis.det_apply,
    Basis.toMatrix_eq_toMatrix_constr]
  rfl

end Cokernel

section Lattice

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem ordFrac_algebraMap_eq_exp {x : R} {n : ℕ} (h : addVal R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R
    (mem_nonZeroDivisors_of_ne_zero hx) ((Ring.ord_eq_addVal x).trans h)]
  rfl

theorem ordFrac_unit_mul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) :
    Ring.ordFrac R (algebraMap R K u * algebraMap R K ϖ ^ n) = WithZero.exp n := by
  rw [map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible hϖ, one_mul,
    ← WithZero.exp_zsmul, smul_eq_mul, mul_one]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R] [Fintype ι] [DecidableEq ι] in
private theorem span_range_coe_basis {A : Submodule R V} (a : Basis ι R A) :
    Submodule.span R (Set.range fun i => (a i : V)) = A := by
  conv_rhs => rw [← Submodule.map_subtype_top A, ← a.span_eq, Submodule.map_span,
    ← Set.range_comp]
  rfl

end Lattice

end GlobalTheory
