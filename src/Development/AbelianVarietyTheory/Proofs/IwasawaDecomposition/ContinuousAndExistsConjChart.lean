import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjChart

open ReciprocityTheory.L2DbarEstimates (V)

noncomputable def conjCoord (d : ℕ) : V d ≃ₜ V d where
  toFun v := WithLp.toLp 2 (star v.ofLp)
  invFun v := WithLp.toLp 2 (star v.ofLp)
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

section

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ}

noncomputable def conjPts (p : Y ⟶ Sp k) (h : σ = (starRingEnd ℂ).comp σ') : CxPts p σ' ≃ₜ CxPts p σ :=
  (Points.conjHomeomorph Y).subtype fun y => by
    have e : spMap σ = spMap (starRingEnd ℂ) ≫ spMap σ' := by
      rw [h, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    change y ≫ p = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ p = _
    rw [e, Category.assoc]
    exact (Points.conjHomeomorph (Sp k)).injective.eq_iff.symm

end

end GlobalTheory.ConjChart
