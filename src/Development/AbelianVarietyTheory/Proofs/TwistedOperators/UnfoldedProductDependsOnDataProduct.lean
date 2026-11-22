import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearLeftLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearRightLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearRightLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.RowVal.conLin_big : Big fun ch => ConLin ch :=
  GlobalTheory.RowReal.big_mono (fun ch h => GlobalTheory.ConnectionLinear.conLin_of_positions ch h.1.1.1 h.1.1.2 h.1.2 h.2)
    (((_root_.GlobalTheory.ConnectionLinear.contrLin_left.and _root_.GlobalTheory.ConLinR.contrLin_one_big).and _root_.GlobalTheory.LastPositionLin.lastLin_zero).and _root_.GlobalTheory.ConnectionLinear.big_lastLin_one)
