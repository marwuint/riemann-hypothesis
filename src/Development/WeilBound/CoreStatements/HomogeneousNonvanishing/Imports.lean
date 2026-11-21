import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRank
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeIntOfProjectiveRingOfIntegers
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGPadic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  intro E _ _ _ H D g
  have := D.fin
  have := D.proj
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank (𝓞 E) g.s D.La
  have := finite_int_of_finite_ringOfIntegers E D.La
  have := finite_int_of_finite_ringOfIntegers E (TwMod g.s D.La)
  have := free_int_of_projective_ringOfIntegers E D.La
  have := free_int_of_projective_ringOfIntegers E (TwMod g.s D.La)
  refine _root_.GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, k1, k2⟩ := tw_g_padic E H.bar H.bar_eq H.unram p D.La (TwMod g.s D.La) D.EF (twForm D g) h3.symm D.alt
    D.unimod D.adj D.alt D.unimod fun a x y => (D.adj (g.s a) x y).trans (by rw [← g.s_bar]; rfl)
  exact _root_.GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry p (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) φ k1 k2

end PositivityTheory.UnitarySelfGeneration
