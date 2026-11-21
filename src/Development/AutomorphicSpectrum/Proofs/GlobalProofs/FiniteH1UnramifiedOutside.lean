import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensions
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndex
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteContinuousCrossedHomomorphisms
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1OfFiniteCrossedHoms

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GSFin

theorem finite_cohomology_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → Finite (cohomology A 1) := by
  intro F Ω _ _ _ _ _ l _ r S _ A _ hA _
  exact _root_.GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles _ _ A (_root_.GlobalTheory.CompanionTheory.Cocycles.finite_cocycles _ _ A hA (_root_.GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite F Ω _ (_root_.GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree F Ω S)))

end GlobalTheory.CompanionTheory.GSFin
