import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcluded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBand
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := _root_.GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand D L P X C tf h
  obtain ⟨hE, hExc⟩ := _root_.GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab D L P X C tf h
  obtain ⟨hG, hH⟩ := _root_.GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes D L P X C tf h
  exact ⟨h.pass, h2, h.rank, _root_.GlobalTheory.NLink.admissible_table_of_conclusion D L P X C tf h h23, _root_.GlobalTheory.NLink.adm5_tab D L P X C tf h,
    _root_.GlobalTheory.NLink.adm6_tab D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    _root_.GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
