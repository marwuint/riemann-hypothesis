import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts

noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

variable (D : D7) (i : D.nd.Loc)

theorem isSSRep_of_mem_twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (hR : ∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) : ∀ p ∈ twList D i Pa R, IsSSRep p.2 := by
  intro p hp
  obtain ⟨k, a, -, rfl⟩ := mem_twList D i hp
  exact ss_twGL _ _ (hR k).2.1

end GlobalTheory.EigenPoint
