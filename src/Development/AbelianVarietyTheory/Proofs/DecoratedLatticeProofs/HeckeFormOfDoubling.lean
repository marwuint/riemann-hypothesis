import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeInnerProductFormulaOfDoublingEuler
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem localZetaOn_all_of_split_inert (D : D7)
    (hs : LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v)
    (hi : LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) :
    LocalZetaOn D (fun _ => True) := by
  intro A L hL χ b hχ hr v _
  by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
  · exact hs A L hL χ b hχ hr v h
  · exact hi A L hL χ b hχ hr v h

theorem paramBoundOn_all_of_split_inert (D : D7)
    (hs : ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v)
    (hi : ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) :
    ParamBoundOn D (fun _ => True) := by
  intro A L hL v _
  by_cases h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
  · exact hs A L hL v h
  · exact hi A L hL v h

end GlobalTheory.Core.Rk.IP
