import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.Model

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem ιMulti_comb {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) K) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = c.det • exteriorPower.ιMulti K m b := by
  have h : (exteriorPower.ιMulti K m).compLinearMap (Fintype.linearCombination K b) =
      (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).smulRight (exteriorPower.ιMulti K m b) := by
    refine (Pi.basisFun K (Fin m)).ext_alternating fun v hv => ?_
    let s : Equiv.Perm (Fin m) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have e : (fun i => Pi.basisFun K (Fin m) (v i)) = (fun i => Pi.basisFun K (Fin m) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K) (fun i => Pi.basisFun K (Fin m) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun h c

omit [NumberField K] in

theorem ιMulti_comb_int {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) (𝓞 K)) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = algebraMap (𝓞 K) K c.det • exteriorPower.ιMulti K m b := by
  have := ιMulti_comb b (c.map (algebraMap (𝓞 K) K))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  rw [← this]
  congr 1
  funext i
  exact Finset.sum_congr rfl fun j _ => (algebraMap_smul K _ _).symm

omit [NumberField K] in

theorem detSpan_span {m : ℕ} (b : Fin m → V) :
    detSpan K m (Submodule.span (𝓞 K) (Set.range b)) = Submodule.span (𝓞 K) {exteriorPower.ιMulti K m b} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨y, hy, rfl⟩
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hy i)
    rw [show y = fun i => ∑ j, (Matrix.of c) i j • b j from funext fun i => (hc i).symm, ιMulti_comb_int]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rintro _ rfl
    exact ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ}

end GlobalTheory.FlatCM.Model

end
