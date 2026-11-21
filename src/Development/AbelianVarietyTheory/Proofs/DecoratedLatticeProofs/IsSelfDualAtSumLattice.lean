import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst

noncomputable section
open scoped Matrix Classical TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Inhab
variable {D : D7}

section Lattice

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

def sumLattice (L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E) :=
  (stdLattice D.host.E t).comap (d.qX.mulVecLin.restrictScalars _) ⊓ (L'.comap (d.q0.mulVecLin.restrictScalars _) ⊓
    (stdLattice D.host.E t).comap (d.qY.mulVecLin.restrictScalars _))

variable {L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}

theorem mem_sumLattice (z : Fin T.rank → D.host.E) : z ∈ sumLattice d L' ↔
    (d.qX *ᵥ z ∈ stdLattice D.host.E t ∧ d.q0 *ᵥ z ∈ L' ∧ d.qY *ᵥ z ∈ stdLattice D.host.E t) := Iff.rfl

end Lattice

theorem exists_good (V : HSp D) : ∃ l : Lvl V, l.Good :=
  let ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  ⟨⟨frameLat V, a⟩, isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, ha⟩

theorem K_eq_lev {V : HSp D} (l : Lvl V) : l.K = GlobalTheory.EisCont.lev V l.L l.c := rfl

end GlobalTheory.RegSch.Inhab
