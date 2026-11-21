import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRungStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodGridFramesOfDepthFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_depFixed : DepFixed → Ascent := fun hD =>
  have hTot : FockTot := _root_.GlobalTheory.ConjDataTotal.fockTot
  have hPart : PartFixed := _root_.GlobalTheory.Asc.partFixed_of_depFixed hD _root_.GlobalTheory.FirstRowDepth.datumDep
  _root_.GlobalTheory.Asc.ascent_of_rungs (_root_.GlobalTheory.AscFin.towerEx_of_depFixed hD) (GlobalTheory.T.nonvanishing_thetaTower_bottom_rung hTot) (_root_.GlobalTheory.AscRungB.rungB hTot hPart)
    (_root_.GlobalTheory.Asc.RungJac.rungJ hTot hPart)

end GlobalTheory.Asc
