import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TypePrimesOfLevel
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataErr
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
