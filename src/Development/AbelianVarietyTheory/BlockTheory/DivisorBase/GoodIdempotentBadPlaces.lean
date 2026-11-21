import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Lev Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 LevDat P0 IsGenericPsi)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (SSParam GoodAt typeChar centralIdem chiTame IsGeneratorFamily)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

variable {D : D7}

abbrev typePl (pb : Fin 2 → 𝓞 D.host.E) : Finset (Pl D.host.E) := primesOf (pb 0 * pb 1)

instance finite_kP (w : Pl D.host.E) : Finite (kP w) :=
  Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot

variable (D) in

def badPl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)

abbrev Model (D : D7) (j : ℕ) : Type 1 := DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))

end GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces
