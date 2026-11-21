import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove

noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000

def New.nMv (_ : TrivialCondition) {D : D7} (m : Mv D) (n : NTiedGPlaceholder D) : NTiedGPlaceholder m.D :=
  @NTiedGPlaceholder.mk _

end UpperTheory.One.M
