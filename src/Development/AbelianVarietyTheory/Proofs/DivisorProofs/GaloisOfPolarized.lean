import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def spehInf (d : ℕ) (A : Multiset ℂ) : Multiset ℂ :=
  ∑ j : Fin d, A.map (· + (((d : ℂ) - 1) / 2 - (j : ℕ)))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

end GlobalTheory.SphGal

end
