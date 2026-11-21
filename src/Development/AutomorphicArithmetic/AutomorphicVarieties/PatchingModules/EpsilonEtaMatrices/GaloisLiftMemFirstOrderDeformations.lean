import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private abbrev SS (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

end Parts
