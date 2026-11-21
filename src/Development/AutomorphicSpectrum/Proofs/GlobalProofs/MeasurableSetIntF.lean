import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

theorem placesCountable (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
