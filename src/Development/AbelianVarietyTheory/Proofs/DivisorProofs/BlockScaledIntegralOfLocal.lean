import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTorus.IntegralOfAdic

theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

end GlobalTheory.ThKTorus.IntegralOfAdic
