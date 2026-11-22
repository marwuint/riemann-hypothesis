import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange

set_option autoImplicit false

noncomputable section

open Module TensorProduct GlobalTheory.DeRham

namespace GlobalTheory.PrincipalPolPairing

section Algebra

variable {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R' M'] {f : M →ₛₗ[algebraMap R R'] M'}

theorem exists_corr (hf : Function.Bijective (liftSemi f)) (h : Dual R M) :
    ∃ h' : Dual R' M', ∀ c, h' (f c) = algebraMap R R' (h c) := by
  let e := LinearEquiv.ofBijective _ hf
  let l : M →ₛₗ[algebraMap R R'] R' :=
    { toFun c := algebraMap R R' (h c), map_add' := by simp, map_smul' := by simp }
  refine ⟨liftSemi l ∘ₗ e.symm.toLinearMap, fun c ↦ ?_⟩
  have : f c = e (1 ⊗ₜ c) := (one_smul R' (f c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem ext_bc (hf : Function.Bijective (liftSemi f)) {N : Type*} [AddCommGroup N] [Module R' N]
    {u v : M' →ₗ[R'] N} (h : ∀ c, u (f c) = v (f c)) : u = v := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hf.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

theorem ext_corr [Module.Finite R M] [Module.Projective R M] (hf : Function.Bijective (liftSemi f))
    {N : Type*} [AddCommGroup N] [Module R' N] {u v : Dual R' M' →ₗ[R'] N}
    (h : ∀ (y : Dual R M) (y' : Dual R' M'), (∀ c, y' (f c) = algebraMap R R' (y c)) → u y' = v y') :
    u = v := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  choose l hl using fun i : Fin n ↦ exists_corr hf (LinearMap.proj i ∘ₗ s)
  refine LinearMap.ext fun y' ↦ ?_
  have e : y' = ∑ i, y' (f (p (Pi.single i 1))) • l i := by
    refine ext_bc hf fun c ↦ ?_
    have hc : c = ∑ i, s c i • p (Pi.single i 1) := by
      conv_lhs => rw [← LinearMap.id_apply (R := R) c, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s c)]
      simp only [map_sum, map_smul]
    conv_lhs => rw [hc]
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hl,
      LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, mul_comm]
    simp
  rw [e]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h _ _ (hl i)]

theorem subsingleton_of_fibres {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (h : ∀ p : PrimeSpectrum R, Subsingleton (AlgebraicClosure p.asIdeal.ResidueField ⊗[R] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have := h p
  have e := AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField p.asIdeal.ResidueField
    (AlgebraicClosure p.asIdeal.ResidueField) Q
  have h₁ := e.toEquiv.subsingleton
  have h₂ : Nontrivial (AlgebraicClosure p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
    (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.rTensor_nontrivial _ _ _
  exact not_subsingleton _ h₁

end Algebra

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase GlobalTheory.DeRhamSheaf
open Limits (pullback)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Affine

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem isotropic (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) A A P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg) P hP ψ hψ
  intro x hx y hy
  have := iso _ (push_mem_Fil (inl A A) hx) _ (push_mem_Fil (inr A A) hy)
  rwa [e, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, sub_zero] at this

end Affine

end GlobalTheory.PrincipalPolPairing
