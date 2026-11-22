import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace PhiModule

open Matrix Module

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {φ : R →+* R}
variable {M : Type*} [AddCommGroup M] [Module R M]

def IsPhiModule (Φ : M →ₛₗ[φ] M) : Prop := Submodule.span R (Set.range Φ) = ⊤

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phiMatrix (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) : Matrix ι ι R :=
  Matrix.of fun i j => b.repr (Φ (b j)) i

theorem phi_basis (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (j : ι) :
    Φ (b j) = ∑ i, phiMatrix b Φ i j • b i := by
  conv_lhs => rw [← b.sum_repr (Φ (b j))]
  rfl

theorem span_range_eq (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    Submodule.span R (Set.range Φ) = Submodule.span R (Set.range (Φ ∘ b)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.range_comp_subset_range _ _))
  rintro _ ⟨x, rfl⟩
  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isPhiModule_iff_isUnit_det (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) :
    IsPhiModule Φ ↔ IsUnit (phiMatrix b Φ).det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_surjective_iff_isUnit, IsPhiModule, span_range_eq b Φ,
    eq_top_iff]
  constructor
  · intro h v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.mem_top (x := b.equivFun.symm v)))
    refine ⟨c, ?_⟩
    have := congrArg b.equivFun hc
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]
    funext i
    simp [Function.comp, phi_basis, map_sum, Finset.sum_apply, mulVec, dotProduct, mul_comm,
      Finsupp.single_apply]
  · intro h x _
    obtain ⟨c, hc⟩ := h (b.equivFun x)
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, ?_⟩
    apply b.equivFun.injective
    rw [← hc]
    funext i
    simp [Function.comp, phi_basis, map_sum, Finset.sum_apply, mulVec, dotProduct, mul_comm,
      Finsupp.single_apply]

variable (R φ) in

structure UnitOrd where

  ord : Rˣ → ℤ
  map_mul : ∀ a b, ord (a * b) = ord a + ord b
  map_phi : ∀ a, ord (Units.map (φ : R →* R) a) = ord a

namespace UnitOrd

variable (v : UnitOrd R φ)

def pow (d : ℕ) : UnitOrd R (φ ^ d) where
  ord := v.ord
  map_mul := v.map_mul
  map_phi a := by
    induction d with
    | zero => congr 1
    | succ d ih =>
      have e : Units.map ((φ ^ (d + 1) : R →+* R) : R →* R) a =
          Units.map (φ : R →* R) (Units.map ((φ ^ d : R →+* R) : R →* R) a) := by
        ext; simp [pow_succ', RingHom.mul_def]
      rw [e, v.map_phi, ih]

end UnitOrd

variable (v : UnitOrd R φ) [Nontrivial R]

def degIn (b : Basis ι R M) (Φ : M →ₛₗ[φ] M) (h : IsPhiModule Φ) : ℤ :=
  v.ord ((isPhiModule_iff_isUnit_det b Φ).1 h).unit

variable [Module.Free R M] [Module.Finite R M]

open Classical in

def deg (Φ : M →ₛₗ[φ] M) : ℤ :=
  if h : IsPhiModule Φ then degIn v (Module.Free.chooseBasis R M) Φ h else 0

def iterate (Φ : M →ₛₗ[φ] M) (d : ℕ) : M →ₛₗ[φ ^ d] M where
  toFun := Φ^[d]
  map_add' x y := by
    induction d with
    | zero => rfl
    | succ d ih => simp only [Function.iterate_succ_apply', ih, map_add]
  map_smul' r x := by
    induction d with
    | zero => simp
    | succ d ih =>
      simp only [Function.iterate_succ_apply', ih, LinearMap.map_smulₛₗ,
        pow_succ', RingHom.mul_def, RingHom.comp_apply]

end PhiModule

end GroundTheory.PAdicHodge
