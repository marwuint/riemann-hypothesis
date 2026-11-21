import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous

open TensorProduct

namespace GlobalTheory

namespace FlatDescent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

variable (A B N) in

def act : B ⊗[A] N →ₗ[B] N := LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

@[simp] theorem act_tmul (b : B) (n : N) : act A B N (b ⊗ₜ n) = b • n := by
  simp [act]

structure IsDescentDatum (θ : N →ₗ[B] B ⊗[A] N) : Prop where
  counit : ∀ n, act A B N (θ n) = n
  coassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) = (TensorProduct.mk A B N 1).lTensor B (θ n)

def invariants (θ : N →ₗ[B] B ⊗[A] N) : Submodule A N :=
  LinearMap.ker (θ.restrictScalars A - TensorProduct.mk A B N 1)

@[simp] theorem mem_invariants {θ : N →ₗ[B] B ⊗[A] N} {n : N} :
    n ∈ invariants θ ↔ θ n = 1 ⊗ₜ n := by
  simp [invariants, sub_eq_zero]

variable (B) in

def canonical (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[B] B ⊗[A] (B ⊗[A] M) :=
  (TensorProduct.mk A B M 1).baseChange B

@[simp] theorem canonical_tmul {M : Type*} [AddCommGroup M] [Module A M] (b : B) (m : M) :
    canonical B M (b ⊗ₜ[A] m) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) := rfl

variable (B) in

theorem isDescentDatum_canonical (M : Type*) [AddCommGroup M] [Module A M] :
    IsDescentDatum (canonical (A := A) B M) := by
  constructor <;> intro x
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [smul_tmul']
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp

variable (B) in

def extend (P : Submodule A N) : B ⊗[A] P →ₗ[B] N := LinearMap.liftBaseChange B P.subtype

@[simp] theorem extend_tmul (P : Submodule A N) (b : B) (n : P) :
    extend B P (b ⊗ₜ n) = b • (n : N) := by
  simp [extend]

theorem act_lTensor_subtype (P : Submodule A N) (x : B ⊗[A] P) :
    act A B N (P.subtype.lTensor B x) = extend B P x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp

theorem apply_extend (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) = (invariants θ).subtype.lTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp [mem_invariants.1 m.2, smul_tmul']

theorem IsDescentDatum.bijective_extend [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : Function.Bijective (extend B (invariants θ)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) _
      (invariants θ).injective_subtype
    rw [← apply_extend, hx, map_zero, map_zero]
  · intro n
    have hex := Module.Flat.lTensor_exact B
      (LinearMap.exact_subtype_ker_map (θ.restrictScalars A - TensorProduct.mk A B N 1))
    obtain ⟨x, hx⟩ := (hex (θ n)).1 (by
      rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h.coassoc, sub_self])
    exact ⟨x, (act_lTensor_subtype (invariants θ) x).symm.trans
      ((congrArg (act A B N) hx).trans (h.counit n))⟩

theorem IsDescentDatum.isBaseChange [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : IsBaseChange B (invariants θ).subtype :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bijective_extend) fun n => by simp

section Amitsur

variable (B) (M : Type*) [AddCommGroup M] [Module A M]

def toInvariants : M →ₗ[A] invariants (canonical (A := A) B M) :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m => by simp

@[simp] theorem coe_toInvariants (m : M) :
    (toInvariants (A := A) B M m : B ⊗[A] M) = 1 ⊗ₜ m := rfl

theorem bijective_toInvariants [Module.FaithfullyFlat A B] :
    Function.Bijective (toInvariants (A := A) B M) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B,
    ← Function.Bijective.of_comp_iff' (isDescentDatum_canonical (A := A) B M).bijective_extend]
  convert Function.bijective_id
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp_all
  | tmul b m => simp [smul_tmul']

def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (canonical B M).restrictScalars A - TensorProduct.mk A B (B ⊗[A] M) 1

@[simp] theorem amitsurDiff_tmul (b : B) (m : M) :
    amitsurDiff B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl

theorem amitsur_exact [Module.FaithfullyFlat A B] :
    Function.Injective (TensorProduct.mk A B M 1) ∧
      Function.Exact (TensorProduct.mk A B M 1) (amitsurDiff (A := A) B M) := by
  refine ⟨Module.FaithfullyFlat.tensorProduct_mk_injective M, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (bijective_toInvariants (A := A) B M).2 ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    simp

end Amitsur

section Morphisms

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

variable (B) in

theorem bijective_baseChange_iff [Module.FaithfullyFlat A B] (g : M →ₗ[A] M') :
    Function.Bijective (g.baseChange B) ↔ Function.Bijective g :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g

end Morphisms

section Invertible

theorem invertible_of_isBaseChange [Module.FaithfullyFlat A B] {M : Type*} [AddCommGroup M]
    [Module A M] {j : M →ₗ[A] N} (hj : IsBaseChange B j) [Module.Invertible B N] :
    Module.Invertible A M := by
  have : Module.Finite A M := Descent.finite_of_isBaseChange hj
  have : Module.Projective A M := Descent.projective_of_isBaseChange hj
  let e : B ⊗[A] (Module.Dual A M ⊗[A] M) ≃ₗ[B] B ⊗[A] A :=
    AlgebraTensorModule.distribBaseChange A B _ _ ≪≫ₗ
      TensorProduct.congr (SymAlg.isBaseChange_dual hj).equiv hj.equiv ≪≫ₗ
        Module.Invertible.linearEquiv B N ≪≫ₗ (AlgebraTensorModule.rid A B B).symm
  have he : (contractLeft A M).baseChange B = e.toLinearMap := by
    ext ξ m
    apply (AlgebraTensorModule.rid A B B).injective
    simp [e, Module.Invertible.linearEquiv, hj.toDual_comp_apply, Algebra.algebraMap_eq_smul_one]
  refine ⟨(bijective_baseChange_iff B _).1 ?_⟩
  rw [he]
  exact e.bijective

theorem IsDescentDatum.invertible_invariants [Module.FaithfullyFlat A B]
    {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) [Module.Invertible B N] :
    Module.Invertible A (invariants θ) :=
  invertible_of_isBaseChange h.isBaseChange

end Invertible

section Gluing

variable (A) in

def smulRight (b : B) : B ⊗[A] N →ₗ[B] B ⊗[A] N :=
  (Algebra.lsmul A A N b).baseChange B

@[simp] theorem smulRight_tmul (b c : B) (n : N) :
    smulRight A b (c ⊗ₜ[A] n) = c ⊗ₜ[A] (b • n) := rfl

def datumOfGluing (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) : N →ₗ[B] B ⊗[A] N :=
  φ ∘ₗ (AlgebraTensorModule.mk A B N B).flip 1

@[simp] theorem datumOfGluing_apply (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) (n : N) :
    datumOfGluing φ n = φ (n ⊗ₜ 1) := rfl

def gluingOfDatum (θ : N →ₗ[B] B ⊗[A] N) : N ⊗[A] B →ₗ[B] B ⊗[A] N :=
  AlgebraTensorModule.lift
    { toFun := fun n =>
        { toFun := fun b => smulRight A b (θ n)
          map_add' := fun b c => by
            induction θ n using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => simp only [map_add, hx, hy]; abel
            | tmul b m => simp [add_smul, tmul_add]
          map_smul' := fun a b => by
            induction θ n using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => simp only [map_add, hx, hy, smul_add]
            | tmul b m => simp }
      map_add' := fun n n' => by ext; simp
      map_smul' := fun b n => by ext; simp }

@[simp] theorem gluingOfDatum_tmul (θ : N →ₗ[B] B ⊗[A] N) (n : N) (b : B) :
    gluingOfDatum θ (n ⊗ₜ b) = smulRight A b (θ n) := rfl

end Gluing

end FlatDescent

end GlobalTheory
