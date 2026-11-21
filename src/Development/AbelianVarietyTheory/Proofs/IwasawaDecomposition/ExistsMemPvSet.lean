import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderSmulOfFix
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.PlaceOverPair

theorem exists_mem_pvSet {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K))
    (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) (v : HeightOneSpectrum (𝓞 H.F)) (hv : OverPF H p v) : ∃ w, w ∈ PvSet H 𝔭 v := by
  obtain ⟨w, h1, h2⟩ := exists_over_both H hp 𝔭 h𝔭 v hv
  refine ⟨w, ?_, h2⟩
  rw [aboveF, Set.Finite.mem_toFinset]
  exact h1

end GlobalTheory.PlaceOverPair
