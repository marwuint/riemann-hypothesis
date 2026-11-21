import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.RealIndexBoundProbe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def withTup (R : RealDat D A Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T)
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (e : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) :
    RealDat D A Ks :=
  { R with mu := mu, twPl := tw, err0 := e }

variable {R : RealDat D A Ks} {F : Face D A}

set_option maxHeartbeats 1000000 in
theorem withTup_nonzeroIndexPlace_iff {mu tw e} (w) : (withTup R mu tw e).NonzeroIndexPlace F w ↔ R.NonzeroIndexPlace F w := Iff.rfl

end GlobalTheory.RealIndexBoundProbe

end
