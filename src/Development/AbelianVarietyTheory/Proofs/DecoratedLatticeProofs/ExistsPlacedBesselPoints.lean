import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarCharacterSquareEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacter

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem oneBlock_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : LevDat D.host.E ℂ V.rank)
    (hn : V.rank ≤ Λ.r) (hs : Λ.s = 0) (hQ : Λ.Q = ∅) (κ : GA D V) :
    (κ ∈ levS V β Λ ↔ κ ∈ GfC V ∧ Lev.finE V κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) β ∧
      Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ) ∈ Λ.P.H) ∧
    Lev.levChi V β Λ κ = ((Formalism.L2.DIV.ext1 Λ.P.H Λ.P.chi
      (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ)) : ℂˣ) : ℂ) := by
  refine ⟨⟨fun h => ?_, fun h => ⟨h.1, ?_⟩⟩, ?_⟩
  · have hl := mem_lev.1 h.2
    exact ⟨h.1, (mem_parLev.1 hl.1).2.1, hl.2⟩
  · refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, h.2.1,
      fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _, fun PP hPP => ?_⟩, h.2.2⟩
    rw [hQ] at hPP
    exact absurd hPP (Finset.notMem_empty _)
  · unfold Lev.levChi levFn
    simp only [hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]

end GlobalTheory.MiTop

end
