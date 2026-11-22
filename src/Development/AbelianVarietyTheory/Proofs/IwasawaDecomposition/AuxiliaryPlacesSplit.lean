import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem isSplitPl_of_mem_levelPrimes {R : Ranks} (H : Host R)
    (hc : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) {p : ℕ} (hp : p ∈ H.levelPrimes)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  obtain ⟨hpr, hm⟩ := hc p hp
  have h := (GlobalTheory.HostSplit.split_of_one_mod R H p hpr hm).1
  obtain ⟨-, he, hf⟩ := GlobalTheory.unramified_degree_one_of_ncard_placesOver H.E p hpr h v hv
  exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSplitPl_of_degree_one H v hf he

end GlobalTheory.HeightCounting.Up
