import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPosition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchange

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem allPositions_holds : AllPositions := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := _root_.GlobalTheory.SymChain.pattern_iter k s κ S t
  have hsupp : S.SupportAt t := _root_.GlobalTheory.SymSupportP.supportAt_of_pattern k s κ S t hpat
  have hclass : S.ClassAt t ν := _root_.GlobalTheory.SymChain.classAt_all k ν hν s κ S t
  exact ⟨_root_.GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt k ν hν s κ S t hclass hsupp, _root_.GlobalTheory.SymChain.ExchangeProof.exchangeAt k ν hν s κ S t hpat⟩

end GlobalTheory.SymChain
