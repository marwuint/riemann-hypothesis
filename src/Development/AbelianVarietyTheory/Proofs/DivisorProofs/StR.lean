import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel

namespace GlobalTheory.PsCo.Pc3

theorem stR : StR := by
  intro n ε
  obtain ⟨hcont, hinv⟩ := _root_.GlobalTheory.offDiagBlockNorm_cont_inv n ε
  exact ⟨hcont, hinv, _root_.GlobalTheory.offDiag_zero_iff_mem_K n ε, _root_.GlobalTheory.isCompact_offDiag_sublevel n ε⟩

end GlobalTheory.PsCo.Pc3
