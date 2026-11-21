import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases.AdmW

open GlobalTheory.AdmLoc

section Ext
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (χ₁ : G →* Oˣ) (z : G → ↥L.T ⊗[O] X)

def actExtL (g : G) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
  LinearMap.prod ((actT L g).rTensor X ∘ₗ LinearMap.fst O _ O +
      (LinearMap.id : O →ₗ[O] O).smulRight (((χ₁ g : Oˣ) : O) • z g) ∘ₗ LinearMap.snd O _ O)
    ((((χ₁ g : Oˣ) : O) • (LinearMap.id : O →ₗ[O] O)) ∘ₗ LinearMap.snd O _ O)

theorem actExtL_apply (g : G) (p : (↥L.T ⊗[O] X) × O) : actExtL L X χ₁ z g p = tableLineDegreeTwo.actExt L X χ₁ z g p := by
  simp [actExtL, tableLineDegreeTwo.actExt, mul_comm]

variable {L X χ₁ z}

variable (L X χ₁ z)

theorem actExtL_ker (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G) :
    tableLineDegreeTwo.kerExt L X lam a ≤ (tableLineDegreeTwo.kerExt L X lam a).comap (actExtL L X χ₁ z g) := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  rintro ⟨m, y⟩ ⟨hm, hy⟩
  simp only [Submodule.mem_bot] at hm
  subst hm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [Submodule.mem_comap, actExtL_apply]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    simp only [tableLineDegreeTwo.actExt, map_zero, zero_add]
    rw [mul_smul, hT, smul_zero]
  · show _ ∈ Ideal.span {lam ^ a}
    simp only [tableLineDegreeTwo.actExt]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem kerExt_kill (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0)
    (m : ((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) : lam ^ a • m = 0 := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    exact hT p.1
  · show _ ∈ Ideal.span {lam ^ a}
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ext
end GlobalTheory.UseLoc.Cases.AdmW
