import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.StdPos

end GlobalTheory.RegSch.StdPos

namespace GlobalTheory.RegSch

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix StdPos

theorem exists_good_frameLat (D : D7) (V : HSp D) : ∃ a, Lvl.Good (⟨frameLat V, a⟩ : Lvl V) :=
  (exists_isMaj V).imp fun _ h => ⟨isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, h⟩

end GlobalTheory.RegSch

end
