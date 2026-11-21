import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (_root_.GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS F Ω S)

end GlobalTheory.CompanionTheory.Hypotheses₂
