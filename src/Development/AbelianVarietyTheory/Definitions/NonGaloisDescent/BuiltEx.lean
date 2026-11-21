import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain

namespace GlobalTheory.CoefDuty

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}

def ExtOf (L₀ L₁ : LocAll (lay0 D)) (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc) : Prop :=
  L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧
    Nonempty (LocExt L₀.lay.fixZ.nd L₁.lay.fixZ.nd L₀.lay.fixZ.naut L₁.lay.fixZ.naut i₀ i₁)

end GlobalTheory.CoefDuty

end
