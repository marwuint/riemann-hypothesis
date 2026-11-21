import Mathlib

open TensorProduct Module
open scoped DirectSum

namespace GlobalTheory
namespace SymAlg

variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

def map (f : M →ₗ[R] M') : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M' :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι R M' ∘ₗ f)

@[simp] theorem map_ι (f : M →ₗ[R] M') (m : M) :
    map f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R M' (f m) := by
  simp [map]

@[simp] theorem map_id : map (LinearMap.id : M →ₗ[R] M) = AlgHom.id R _ := by
  ext m; simp

theorem map_comp (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map (g ∘ₗ f) = (map g).comp (map f) := by
  ext m; simp

variable (R M) in

def homog (d : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ d

theorem ι_mem_homog (m : M) : SymmetricAlgebra.ι R M m ∈ homog R M 1 := by
  simpa only [homog, pow_one] using LinearMap.mem_range_self _ m

instance gradedMonoid : SetLike.GradedMonoid (homog R M) :=
  Submodule.nat_power_gradedMonoid _

variable (R M) in

def gradedι : M →ₗ[R] ⨁ i : ℕ, homog R M i :=
  DirectSum.lof R ℕ (fun i => homog R M i) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ ι_mem_homog

theorem gradedι_apply (m : M) :
    gradedι R M m = DirectSum.of (fun i : ℕ => homog R M i) 1
      ⟨SymmetricAlgebra.ι R M m, ι_mem_homog m⟩ := rfl

instance gradedAlgebra : GradedAlgebra (homog R M) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (gradedι R M))
    (by
      ext m
      change DirectSum.coeAlgHom (homog R M)
        (SymmetricAlgebra.lift (gradedι R M) (SymmetricAlgebra.ι R M m)) = SymmetricAlgebra.ι R M m
      rw [SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.coeAlgHom_of])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

instance projective [Module.Projective R M] : Module.Projective R (SymmetricAlgebra R M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective R M›
  refine Module.Projective.of_split (map s).toLinearMap
    (map (Finsupp.linearCombination R id)).toLinearMap ?_
  rw [← AlgHom.comp_toLinearMap, ← map_comp, hs, map_id]
  rfl

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]

variable (S) in

def mapOver (j : M →ₗ[R] W) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι S W).restrictScalars R ∘ₗ j)

@[simp] theorem mapOver_ι (j : M →ₗ[R] W) (m : M) :
    mapOver S j (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S W (j m) := by
  simp [mapOver]

variable (S) in

noncomputable def baseChangeHom (j : M →ₗ[R] W) :
    S ⊗[R] SymmetricAlgebra R M →ₐ[S] SymmetricAlgebra S W :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (mapOver S j) (fun _ _ => Commute.all _ _)

@[simp] theorem baseChangeHom_tmul (j : M →ₗ[R] W) (s : S) (x : SymmetricAlgebra R M) :
    baseChangeHom S j (s ⊗ₜ x) = s • mapOver S j x := by
  simp [baseChangeHom, Algebra.smul_def, Algebra.ofId_apply]

noncomputable def baseChangeEquiv {j : M →ₗ[R] W} (h : IsBaseChange S j) :
    S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S W :=
  AlgEquiv.ofAlgHom (baseChangeHom S j)
    (SymmetricAlgebra.lift
      (h.lift ((TensorProduct.mk R S (SymmetricAlgebra R M) 1) ∘ₗ SymmetricAlgebra.ι R M)))
    (by
      refine SymmetricAlgebra.algHom_ext (h.algHom_ext _ _ fun m => ?_)
      simp [h.lift_eq])
    (by
      ext m
      simp [h.lift_eq, Algebra.TensorProduct.one_def])

@[simp] theorem baseChangeEquiv_tmul {j : M →ₗ[R] W} (h : IsBaseChange S j) (s : S)
    (x : SymmetricAlgebra R M) : baseChangeEquiv h (s ⊗ₜ x) = s • mapOver S j x :=
  baseChangeHom_tmul j s x

theorem isBaseChange_dual [Module.Finite R M] [Module.Projective R M] {j : M →ₗ[R] W}
    (h : IsBaseChange S j) : IsBaseChange S h.toDual := by
  let Φ : S ⊗[R] Dual R M →ₗ[S] Dual S W := h.toDual.liftBaseChange S
  let e := lTensorHomEquivHomLTensor R M S R
  have key : ∀ (t : S ⊗[R] Dual R M) (m : M), Φ t (j m) = TensorProduct.rid R S (e t m) := by
    intro t m
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul s ξ =>
      simp [Φ, e, h.toDual_comp_apply, Algebra.smul_def, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨?_, ?_⟩)
    (fun ξ => by change Φ _ = _; simp [Φ])
  · rw [injective_iff_map_eq_zero]
    intro t ht
    apply e.injective
    ext m
    apply (TensorProduct.rid R S).injective
    rw [← key, ht]
    simp
  · intro φ
    refine ⟨e.symm ((TensorProduct.rid R S).symm.toLinearMap ∘ₗ φ.restrictScalars R ∘ₗ j), ?_⟩
    refine h.algHom_ext _ _ fun m => ?_
    rw [key]
    simp

end BaseChange

end SymAlg
end GlobalTheory
