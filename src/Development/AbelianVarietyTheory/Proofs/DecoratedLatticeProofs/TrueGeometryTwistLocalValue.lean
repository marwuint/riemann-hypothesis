import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.FinData

theorem isFinComb_smul {D : D7} {S T : HSp D} (r : ℂ) (c : WO S T →₀ ℂ) (h : GlobalTheory.SeeSaw.IsFinComb c) :
    GlobalTheory.SeeSaw.IsFinComb (r • c) := fun u hu => h u (Finsupp.support_smul hu)

end GlobalTheory.Fam.FinData
