import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCaseStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentPointLastIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel

set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.DefCore

theorem unitE_nonneg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) : 0 ≤ unitE p := by
  rw [hw.unit]
  have hx : 0 < L.sc.x := by linarith [hh.big.2.1, hh.big.2.2.1]
  have hb : 0 < L.sc.b := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx _) _) hh.room
  have := hh.big.2.2.2
  have : (0:ℝ) ≤ L.sc.L := by linarith [hh.big.2.1]
  positivity

end GlobalTheory.CovTop.DefCore

end
