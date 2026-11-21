import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def PsiRat (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∀ x : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D x)) = 1

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

def IsQuotPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ

end Scalar

end Formalism.IndefR.Mi

end
