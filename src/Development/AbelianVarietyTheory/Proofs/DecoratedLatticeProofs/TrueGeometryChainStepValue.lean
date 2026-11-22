import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeFinal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PenVol

theorem relIndex_ne_zero_of_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U U0 : Subgroup G)
    (hU0 : U0 ≤ K) (hc : IsCompact (U0 : Set G)) (ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K)) :
    U.relIndex U0 ≠ 0 := by
  haveI : CompactSpace U0 := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous (fun x : U0 => (⟨x.1, hU0 x.2⟩ : K)) := Continuous.subtype_mk continuous_subtype_val _
  have ho' : IsOpen ((U.subgroupOf U0 : Subgroup U0) : Set U0) := ho.preimage hcont
  haveI : Finite (U0 ⧸ U.subgroupOf U0) := (U.subgroupOf U0).quotient_finite_of_isOpen ho'
  haveI : (U.subgroupOf U0).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero

theorem wt_cast (C : ℕ → Type) (w : ∀ j, C j → ℂ) {j j' : ℕ} (h : j = j') (x : C j) :
    w j' (cast (congrArg C h) x) = w j x := by
  subst h; rfl

end GlobalTheory.PenVol

end
