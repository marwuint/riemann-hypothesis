import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition

noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem map_eq_sum (j : V →ₛₗ[σ] H) (b : Module.Basis ι K V) (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smulₛₗ]

theorem exists_cx (hli : LinearIndependent ℂ fun i => j (b i)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (f : Module.End K V) : ∃ U : Module.End ℂ H, ∀ v, U (j v) = j (f v) := by
  have h2 : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [map_eq_sum j b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i)), fun v => ?_⟩
  have h3 : ∀ i, ((Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i))) (j (b i)) = j (f (b i)) := fun i => by
    have := (Module.Basis.mk hli h2).constr_basis ℂ (fun i => j (f (b i))) i
    rwa [Module.Basis.mk_apply] at this
  rw [map_eq_sum j b v, map_sum]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, map_smulₛₗ, h3]

theorem ext_of_span {X : Type} [AddCommGroup X] [Module ℂ X] (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    {f g : H →ₗ[ℂ] X} (h : ∀ v, f (j v) = g (j v)) : f = g :=
  LinearMap.ext_on_range hsp h

theorem sum_selfAdj {G : Type} [Group G] [Fintype G] (r : Representation K G V) (a : G → K)
    (ha : ∀ g, starRingEnd ℂ (σ (a g)) = σ (a g⁻¹))
    (hr : ∀ g v w, inner ℂ (j (r g v)) (j (r g w)) = inner ℂ (j v) (j w)) (v w : V) :
    inner ℂ (j ((∑ g, a g • r g) v)) (j w) = inner ℂ (j v) (j ((∑ g, a g • r g) w)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, ha]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [Equiv.inv_apply, ← hr g v, ← Module.End.mul_apply (r g) (r g⁻¹), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

end Linear

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_form : (LinearIndependent ℂ fun i => j (S.basis i)) ∧ Submodule.span ℂ (Set.range j) = ⊤ ∧
    ∀ x y, inner ℂ (j x) (j y) = σ (S.csum (x : S.Cl → S.V) (y : S.Cl → S.V)) := by
  obtain ⟨-, h2, ⟨h3, h4⟩, -⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨LinearIndependent.of_comp M.e (by simpa only [Function.comp_def, hj] using h3), ?_, fun x y => ?_⟩
  · refine Submodule.map_injective_of_injective hM.1 ?_
    rw [Submodule.map_top, hM.2.1, ← h4, Submodule.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hj]
  · rw [hM.2.2, hj, hj]
    exact h2 x y

end Pres

theorem idem_idem {K G E : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {X : Finset (G → K)} (hX : ∀ c ∈ X, IsAbsIrrChar c) (ρ : Representation ℂ G E) (z : E) :
    ∑ g, σ ((idemOf X).coeff g) • ρ g (∑ h, σ ((idemOf X).coeff h) • ρ h z) = ∑ h, σ ((idemOf X).coeff h) • ρ h z := by
  conv_rhs => rw [← idemOf_mul_self X hX]
  simp only [coeff_mul_fin, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm (f := fun h x => (σ ((idemOf X).coeff x) * σ ((idemOf X).coeff (x⁻¹ * h))) • ρ h z)]
  refine Finset.sum_congr rfl fun g _ => Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  simp [mul_smul]

theorem mem_range_adjoint_tw {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (s : Bool) (f : E →ₗ[ℂ] E') (y : E) :
    Tw.mk s y ∈ LinearMap.range (LinearMap.adjoint (Tw.map s f)) ↔ y ∈ LinearMap.range (LinearMap.adjoint f) := by
  have : Tw.map s (LinearMap.adjoint f) = LinearMap.adjoint (Tw.map s f) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [Tw.inner_eq, Tw.inner_eq]
    exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))
  rw [← this]
  exact Iff.rfl

end GlobalTheory.AdjBlock

end
