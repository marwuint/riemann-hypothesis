import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
  {M : RatModel (𝓞 K) Ω}

theorem const_val {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K))) (a : K) :
    algebraMap K Ω a ∈ M.O (y (IsLocalRing.closedPoint ℂ)) ∧ M.val y (algebraMap K Ω a) = σ a := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hr := range_eq_singleton y (IsLocalRing.closedPoint ℂ)
  have hq0 : algebraMap (𝓞 K) K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hσq : σ (algebraMap (𝓞 K) K q) ≠ 0 := (map_ne_zero σ).2 hq0
  have hv := fun c => val_algebraMap hy c
  have hu : IsUnit (⟨algebraMap (𝓞 K) Ω q, Subalgebra.algebraMap_mem _ q⟩ :
      M.O (y (IsLocalRing.closedPoint ℂ))) := (val_ne_zero_iff hr _).1 (by rw [hv]; exact hσq)
  obtain ⟨h0, hi⟩ := (isUnit_O_iff _).1 hu
  dsimp only at h0 hi
  have e : algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) =
      algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ := by
    rw [map_div₀, div_eq_mul_inv, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hm : algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ ∈ M.O (y (IsLocalRing.closedPoint ℂ)) :=
    mul_mem (Subalgebra.algebraMap_mem _ p) hi
  rw [e]
  refine ⟨hm, ?_⟩
  have h1 := val_mul (specializes_of_range_eq hr) hm (Subalgebra.algebraMap_mem _ q)
  rw [inv_mul_cancel_right₀ h0, hv, hv] at h1
  rw [map_div₀, eq_div_iff hσq]
  exact h1.symm

theorem exists_coord {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K)))
    (ev : V →ₗ[K] Ω) (c : Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) {S : Set V} (hS : Submodule.span K S = ⊤)
    (hc : ∀ v ∈ S, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ))) :
    ∃ x : Fin N → ℂ, ∀ v, M.val y (ev v / c) = ∑ j, σ (b.repr v j) * x j := by
  have hr := specializes_of_range_eq (range_eq_singleton y (IsLocalRing.closedPoint ℂ))
  have hsm : ∀ (a : K) v, ev (a • v) / c = algebraMap K Ω a * (ev v / c) := fun a v => by
    rw [map_smul, Algebra.smul_def, mul_div_assoc]
  have hall : ∀ v, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ)) := fun v => by
    have hv : v ∈ Submodule.span K S := hS ▸ trivial
    induction hv using Submodule.span_induction with
    | mem _ h => exact hc _ h
    | zero => rw [map_zero, zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
    | smul a v _ hv => rw [hsm]; exact mul_mem (const_val hy a).1 hv
  let ℓ : V →+ ℂ :=
    { toFun := fun v => M.val y (ev v / c)
      map_zero' := by rw [map_zero, zero_div]; exact val_zero y
      map_add' := fun a b => by rw [map_add, add_div]; exact val_add hr (hall a) (hall b) }
  refine ⟨fun j => ℓ (b j), fun v => ?_⟩
  change ℓ v = _
  conv_lhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change M.val y _ = _
  rw [hsm, val_mul hr (const_val hy _).1 (hall _), (const_val hy _).2]
  rfl

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

