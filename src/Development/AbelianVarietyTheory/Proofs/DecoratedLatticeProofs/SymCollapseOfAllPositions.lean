import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnIndicatorPureAtSymmetricPosition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowIndicatorOfSymLevelExchange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnSupportOfOneIndexAtSymPosition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelDoubleStepOfFlatColumnFlatRow

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat

theorem symCollapse_of_allPositions : AllPositions → GlobalTheory.LocFlat.SymCollapse := by
  intro hA k _ _ _ _ _ _ ν hν s κ S t _ _
  obtain ⟨hO, hE⟩ := hA k ν hν s κ S t
  have hP : S.Pattern t := GlobalTheory.SymChain.pattern_iter k s κ S t
  have hC := _root_.GlobalTheory.LocFlat.pureCol_of_pattern k ν hν s κ S t hP hE
  have hR := _root_.GlobalTheory.LocFlat.pureRow_of_exchange k ν hν s κ S t hP hE
  exact ⟨_root_.GlobalTheory.LocFlat.suppCol_of_oneIndexAt k ν hν s κ S t hO, hC, hR, _root_.GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow k ν hν s κ S t hP hO hC hR⟩

end GlobalTheory.LocFlat
