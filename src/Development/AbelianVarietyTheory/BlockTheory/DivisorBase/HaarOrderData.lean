import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop :=
  1800 < D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : Fin D.R.m) (h : j.1 + 1 < D.R.m),
    (D.R.t : ℚ) + 2 * (bigN D : ℚ) ^ 3 < (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).b j

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

end GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions

end
