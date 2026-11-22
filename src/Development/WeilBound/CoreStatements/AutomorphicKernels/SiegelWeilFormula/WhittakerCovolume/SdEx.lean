import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianAdeles
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuples

namespace PositivityTheory.SiegelWeilFormula.KWhit

theorem sdEx : SdEx := by
  intro F E _ _ _ _ _ σ hcm M J hJ ψ hψ n
  exact ⟨_root_.GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples F E σ hcm M J hJ ψ hψ n, _root_.GlobalTheory.CompanionTheory.SW.HermCoord.exists_sdHerm F E σ hcm ψ hψ n⟩

end PositivityTheory.SiegelWeilFormula.KWhit
