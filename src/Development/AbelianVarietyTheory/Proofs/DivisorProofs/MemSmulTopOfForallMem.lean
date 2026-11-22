import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalOfFreeHodgeBaseChangeRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

namespace GlobalTheory.BirigLift

theorem mem_smul_top_of_forall_mem {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P) (hx : ∀ c, x c ∈ I) :
    x ∈ I • (⊤ : Submodule R (Module.Dual R P)) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : x = ∑ i, x (f (Pi.single i 1)) • ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ s) := by
    ext c
    have hc : c = f (s c) := (LinearMap.congr_fun hs c).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    conv_lhs => rw [hc, pi_eq_sum_univ (s c), map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    congr 3
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx _) trivial

theorem apply_mem_of_mem_smul_top {R : Type} [CommRing R] (I : Ideal R) {P : Type*} [AddCommGroup P] [Module R P]
    {x : Module.Dual R P} (hx : x ∈ I • (⊤ : Submodule R (Module.Dual R P))) (c : P) : x c ∈ I := by
  refine Submodule.smul_induction_on (p := fun y : Module.Dual R P ↦ y c ∈ I) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
  · rw [LinearMap.smul_apply, smul_eq_mul]; exact I.mul_mem_right _ hr
  · rw [LinearMap.add_apply]; exact I.add_mem hy hz

theorem exists_perfect_mod {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {D H : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R₀ H] (red : D →ₛₗ[π] H)
    (φ : D →ₗ[R] D →ₗ[R] R) (ψ : H →ₗ[R₀] H →ₗ[R₀] R₀) (hπ : Function.Surjective π)
    (hψ : Function.Surjective ψ.flip) (hred : Function.Surjective red)
    (hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule R D))
    (hrel : ∀ x y, ψ (red x) (red y) = π (φ x y)) (l : D →ₗ[R] R) :
    ∃ z, ∀ x, l x - φ x z ∈ RingHom.ker π := by
  have hl : ∀ x, x ∈ (RingHom.ker π) • (⊤ : Submodule R D) → π (l x) = 0 := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun y : D ↦ π (l y) = 0) hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
    · rw [map_smul, smul_eq_mul, map_mul, RingHom.mem_ker.1 hr, zero_mul]
    · rw [map_add, map_add, hy, hz, add_zero]
  let s := Function.surjInv hred
  have hs : ∀ h, red (s h) = h := Function.surjInv_eq hred
  have key : ∀ x x', red x = red x' → π (l x) = π (l x') := fun x x' e ↦ by
    have := hl (x - x') (hker _ (by rw [map_sub, e, sub_self]))
    rwa [map_sub, map_sub, sub_eq_zero] at this
  let l₀ : H →ₗ[R₀] R₀ :=
    { toFun h := π (l (s h))
      map_add' a b := by
        rw [key (s (a + b)) (s a + s b) (by rw [map_add, hs, hs, hs]), map_add, map_add]
      map_smul' r h := by
        obtain ⟨r', rfl⟩ := hπ r
        rw [key (s (π r' • h)) (r' • s h) (by rw [map_smulₛₗ, hs, hs]), map_smul, smul_eq_mul, map_mul]
        rfl }
  obtain ⟨w, hw⟩ := hψ l₀
  obtain ⟨z, rfl⟩ := hred w
  refine ⟨z, fun x ↦ RingHom.mem_ker.2 ?_⟩
  have e := LinearMap.congr_fun hw (red x)
  rw [LinearMap.flip_apply, hrel] at e
  rw [map_sub, e, sub_eq_zero]
  exact key _ _ (hs _).symm

end GlobalTheory.BirigLift

namespace GlobalTheory.BirigLift

end GlobalTheory.BirigLift

namespace GlobalTheory.BirigLift

end GlobalTheory.BirigLift
