import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistsAtLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimeLtScaleBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightOnePlacesAreTwistPlacesOfWitness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BwitFrameTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEListPinPt

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

section Transfer

variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem fieldHas_of_same {G G₀ : GridData Lc sc} {K : Type} [Field K] {e : K →+* ℂ} (hv : G.pl.v0 = G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) (h : FieldHas G₀ e) : FieldHas G e := by
  have hS : G.pl.S0 = G₀.pl.S0 := by unfold Places.S0; rw [hv]
  have hd : ∀ v, G.pl.depth sc v = G₀.pl.depth sc v := fun v => by unfold Places.depth; rw [hv]
  refine ⟨fun i h1 h2 => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    have := hch ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact h.values _ h1 h2
  · rw [hd]
    exact h.roots v (hS ▸ hv')

theorem lamOf_of_same {G G₀ : GridData Lc sc} (hw : G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) : lamOf G = lamOf G₀ := by
  unfold lamOf
  rw [hw]
  congr 1
  funext a
  exact hch a

end Transfer

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridFit_of_parts {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hp : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (h1 : Formalism.L2.Host.ValLL0 D p.R.C) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D))
    (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G :=
  ⟨h1, h2, hs, hc, hp, h3, h4⟩

end GlobalTheory.Mem.LiteralAutomorphy.GridRow

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

end GlobalTheory.Mem.LiteralAutomorphy.GridRow
