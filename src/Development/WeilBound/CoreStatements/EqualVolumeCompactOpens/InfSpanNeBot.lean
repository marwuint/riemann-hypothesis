import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LevelIdeal

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree

def levIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) : Ideal (𝓞 E) :=
  l.Mb ⊓ Ideal.span {(l.A : 𝓞 E)}

theorem inf_span_ne_bot {R : Type} [CommRing R] [IsDomain R] {I J : Ideal R} {m a : R} (h : I * J = Ideal.span {m})
    (hm : m ≠ 0) (ha : a ≠ 0) : I ⊓ Ideal.span {a} ≠ ⊥ := by
  have h1 : m ∈ I * J := h ▸ Ideal.mem_span_singleton_self m
  have h2 : m * a ∈ I ⊓ Ideal.span {a} :=
    ⟨I.mul_mem_right _ (Ideal.mul_le_inf h1).1, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩
  intro h0
  rw [h0] at h2
  exact mul_ne_zero hm ha h2

end PositivityTheory.EqVol
