import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem const_zero (C : IntegralChartA3 Xo c T io y) :
    (∀ j, MvPowerSeries.constantCoeff (C.FT j) = 0) ∧ ∀ a j, MvPowerSeries.constantCoeff (C.actT a j) = 0 := by
  letI := io.toAlgebra
  obtain ⟨⟨h1, h2, -⟩, -⟩ := C.gen
  refine ⟨fun j => ?_, fun a j => ?_⟩
  · have := C.ch.B.G.const j
    rw [h1 j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this
  · have := C.ch.B.A.const a j
    rw [h2 a j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this

theorem dim_eq (C : IntegralChartA3 Xo c T io y) : chD C.ch = Fintype.card (Lt1 Dw) := by
  letI := io.toAlgebra
  let f : (Lt1 Dw → T.Fr) →ₗ[T.Fr] (Fin C.ch.d → T.Fr) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * C.ch.uvec ℓ j
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by funext j; simp [Finset.mul_sum, _root_.mul_assoc] }
  have hb : Function.Bijective f := (Function.bijective_iff_existsUnique f).2 fun v => by
    obtain ⟨a, ha, hu⟩ := C.ch.chart.basis v
    exact ⟨a, funext ha, fun b hb => hu b (congrFun hb)⟩
  have := (LinearEquiv.ofBijective f hb).finrank_eq
  simpa using this.symm

end GlobalTheory.IntChartCheck
