import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdentityCosetEntryProportionalColumnDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumCompletionEqColumnTestFunctionStatement

namespace GlobalTheory.SymBridge

theorem matchAtType : MatchAtType := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν h
  exact ⟨_root_.GlobalTheory.EntryBridge.entry_agree X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    _root_.GlobalTheory.SymBridge.psiAgree_of_atType X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.stepDatum_completion_eq_columnTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h⟩

end GlobalTheory.SymBridge
