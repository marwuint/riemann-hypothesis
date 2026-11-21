import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ElementDenominator

noncomputable section

namespace PI.Dv.IdxW

open Module

section Gen

variable {R : Type*} [CommRing R] (S : Submonoid R)

variable {V : Type*} [AddCommGroup V] [Module R V]

def lenS (M N : Submodule R V) : ℕ∞ :=
  Module.length (Localization S) (LocalizedModule S (↥M ⧸ N.comap M.subtype))

end Gen

section Frac

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable (K) in
include K in
theorem smul_eq_zero_iff' {c : R} (hc : c ≠ 0) {x : V} : c • x = 0 ↔ x = 0 := by
  rw [← algebraMap_smul K c x, smul_eq_zero]
  have : algebraMap R K c ≠ 0 := by
    intro h
    exact hc ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  simp [this]

theorem eltDen (Y : Submodule R V) {y : V} (hy : y ∈ Submodule.span K (Y : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ElementDenominator.eltDen Y hy

def toSpan (M : Submodule R V) : ↥M →ₗ[R] ↥(Submodule.span K (M : Set V)) where
  toFun x := ⟨x, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance isLocalizedModule_toSpan (M : Submodule R V) :
    IsLocalizedModule (nonZeroDivisors R) (toSpan (K := K) M) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hx' : algebraMap R K x ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      apply Subtype.ext
      have : (x : R) • ((y : V) - z) = 0 := by
        rw [smul_sub, sub_eq_zero]
        exact congrArg Subtype.val hyz
      exact sub_eq_zero.mp ((smul_eq_zero_iff' K hx0).mp this)
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      apply Subtype.ext
      show (x : R) • ((algebraMap R K x)⁻¹ • (y : V)) = y
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hx', one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := eltDen (K := K) M y.2
    refine ⟨(⟨s • (y : V), hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
    apply Subtype.ext
    rfl
  exists_of_eq {x₁ x₂} h := by
    refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    have : x₁ = x₂ := Subtype.ext h'
    rw [this]

end Frac

end PI.Dv.IdxW
