import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.TowerModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Laws

variable (W : Tower D)

theorem cxp_triv : W.CXP W.triv = W.CX := rfl

end Laws

end GlobalTheory.Core.Rk.TowerModel

end
