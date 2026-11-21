import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.TraceSingleMulSingle
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.PeriodIntegrals.HookBound
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.Der

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OmFar

open Formalism.IndefR.Fock.DRho
open scoped TensorProduct

theorem finPart_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := by
  have h0 : finHom V g = 1 := hg
  have h : (finHom V g).1 = 1 := by rw [h0]; rfl
  exact h

end OmFar

end Formalism.IndefR.Fock.Der

end
