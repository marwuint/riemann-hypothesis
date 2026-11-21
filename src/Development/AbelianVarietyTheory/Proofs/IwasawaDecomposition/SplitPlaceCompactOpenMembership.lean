import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocLevel

theorem mem_placesOver_of_overPl' {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem overPl_of_isConjPl {D : D7} {w : PlE D.host} {s : SplitPlace D.host.E} (hc : IsConjPl D.host w s.w) :
    NG.OverPl w s.v := by
  unfold NG.OverPl
  rw [← s.w_under]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  apply hc
  have hy := GlobalTheory.SplitConjPlace.cO_algebraMap a
  set y := algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a
  have e1 : (y : D.host.E) = IsCMField.complexConj D.host.E (y : D.host.E) := by
    conv_lhs => rw [← hy]
    rw [IsCMField.coe_ringOfIntegersComplexConj]
  rw [e1]
  conv_rhs => rw [← e1]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

end GlobalTheory.LocLevel
