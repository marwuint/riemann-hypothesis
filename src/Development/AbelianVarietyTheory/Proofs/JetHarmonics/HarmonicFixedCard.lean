import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedFrameGauge
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BiadditiveBalancedSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion

section Letters

variable {E : Type} [Field E] [NumberField E] {k : Type} [Field k]

theorem conj_eq [IsCMField E] (τ : E →+* k) : BalancedFrameGauge.conjType E τ = BiadditiveBalancedSeries.conjEmb τ := rfl

theorem harmonic_iff [IsCMField E] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) :
    BalancedFrameGauge.IsHarmonic r P ↔ BiadditiveBalancedSeries.IsHarmonic r P := Iff.rfl

theorem eigen_eq [StarRing (𝓞 E)] {R : Type} [CommRing R] [Algebra R k] {d : ℕ} (B : FB R d (𝓞 E))
    (τ : E →+* k) : BalancedFrameGauge.lieEigen k B τ = BiadditiveBalancedSeries.lieEig B τ := rfl

end Letters

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion
