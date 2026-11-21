import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SeeSawFourier
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummand
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourierStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.LocFlat.CFac
open GlobalTheory.FinPl (SplitPt)
open GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier (atW beta nrm OppLines IsLineFrame ofCol ofRow LineFourier SeeSawFourier)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastCompare

theorem map_mem_integer {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (φ : k →* k') (hφ : Continuous φ)
    {a : k} (ha : a ∈ 𝒪[k]) : φ a ∈ 𝒪[k'] := by
  by_contra h
  rw [Valuation.mem_integer_iff, not_le] at h
  have hK : IsCompact (φ '' (𝒪[k] : Set k)) := (isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[k])).image hφ
  haveI : MulArchimedean (ValueGroupWithZero k') := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h0 : valuation k' (φ a) ≠ 0 := (zero_lt_one.trans h).ne'
  have hU : ∀ n : ℕ, IsOpen {y : k' | valuation k' y < valuation k' (φ a) ^ n} := fun n => by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset ((IsValuativeTopology.hasBasis_nhds y).mem_of_mem (i := Units.mk0 _ (pow_ne_zero n h0)) trivial) ?_
    intro z hz
    have := (valuation k').map_add_lt hz hy
    simpa using this
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ hU (fun y _ => by
      obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k' y) h
      exact Set.mem_iUnion.2 ⟨n + 1, hn.trans_lt (pow_lt_pow_right₀ h n.lt_succ_self)⟩)
    (directed_of_isDirected_le fun m n hmn y hy => lt_of_lt_of_le hy (pow_le_pow_right₀ h.le hmn))
  have := hn ⟨a ^ n, pow_mem ha n, rfl⟩
  simp at this

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' n n' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n']

variable {q : SplitPt D k} {S T : HSp D} {s : k} {σ : Y' ≃ n'} {σ' : Y ≃ n} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
  {α : GlobalTheory.FinPl.Frame q S n'} {β : GlobalTheory.FinPl.Frame q T n}

end GlobalTheory.LastCompare

end
