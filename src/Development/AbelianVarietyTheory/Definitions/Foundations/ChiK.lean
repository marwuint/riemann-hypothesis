import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def chiK (l : ℕ) [Fact l.Prime] (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

end GlobalTheory.K4
