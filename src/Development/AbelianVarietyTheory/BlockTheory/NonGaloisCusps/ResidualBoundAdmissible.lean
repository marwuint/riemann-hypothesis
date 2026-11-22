import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def AdmPl (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (P : PlE D.host) : Prop :=
  P ∉ S ∧ IsSplitPl D.host P ∧ DecV N P ≤ H

variable {X} (bkP : BKPh X)

end GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

end
