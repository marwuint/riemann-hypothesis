import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def UnitOff (N : ℕ) (u : ℂ) : Prop :=
  u ≠ 0 ∧ ∃ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ n * u) ∧ IsIntegral ℤ ((N : ℂ) ^ n * u⁻¹)

end GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

end
