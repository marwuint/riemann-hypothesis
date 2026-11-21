import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsDivisionOfMOne

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem isEtPlace_of_isUnit (b : Base D R) (hp : IsUnit (p : R)) (w0 : Ideal (𝓞 D.F)) (h : w0.IsMaximal)
    (hw : (p : 𝓞 D.F) ∈ w0) : IsEtPlace b w0 := by
  refine ⟨h, hw, fun i => ?_, fun k _ _ β φ _ => ?_⟩
  · refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, hw, by simp⟩) hp
  · exfalso
    have := hp.map β
    simp at this

end GlobalTheory.UPel.HT.EtLev
