import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwoOf
import Development.WeilBound.ThetaLifts.TowerModels.LeviEx
import Development.WeilBound.ThetaLifts.TowerModels.PlaneSkew
import Development.WeilBound.ThetaLifts.TowerModels.StabEx
import Development.WeilBound.ThetaLifts.TowerModels.ModelEx
import Mathlib

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

end PositivityTheory.ThKG.Tow

end
