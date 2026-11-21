import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularQuotientNearPrimeFiniteTypeInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRegularLocusOfNagata
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem qeRing_of_finiteType_int : ∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], FinalTheorems.QERing A := by
  intro A _ _
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  refine ⟨hN, fun P _ => ⟨?_, ?_⟩, fun B _ _ _ => ?_⟩
  · exact AdicCompletion.flat_of_isNoetherian _
  · apply _root_.GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType
    intro K _ _ _
    haveI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
      Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime P) :=
      Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime P)
    have hZ : @Algebra.EssFiniteType ℤ (Localization.AtPrime P) _ _ (Ring.toIntAlgebra _) := by
      convert this
      exact Subsingleton.elim _ _
    exact @_root_.GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int (Localization.AtPrime P) K _ _ hZ _ _ _
  · haveI : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A) ‹_›
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    exact _root_.GlobalTheory.isOpen_regularLocus_of_nagata B (fun p _ => _root_.GlobalTheory.generically_regular_quotient_of_finiteType_int B p)

end GlobalTheory
