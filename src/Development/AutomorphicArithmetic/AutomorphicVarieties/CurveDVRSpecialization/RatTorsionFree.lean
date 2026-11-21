import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyUnramifiedCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut

namespace UpperTheory.V.Pr

instance (priority := high) ratTorsionFree (Ω : Type) [Field Ω] [CharZero Ω] : Module.IsTorsionFree ℚ Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

section Ord

variable (l : ℕ) {O : Type} [CommRing O] [IsLocalRing O] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω)
  (B : ValuationSubring Ω)

structure OrdPt {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A] (r : G ℚ Ω →* GG 3 A) : Prop where
  red : UnitaryThreeInertia.Red η Ψ r
  cont : UnitaryThreeInertia.AdicCont (maximalIdeal A) r
  norm : Normalised σ g₁ r
  away : ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B', η s = 1 → Ψ s = 1 → r s = 1
  ord : UnitaryThreeInertia.CondT (η.comp (Dec (F := ℚ) B).subtype) (Ψ.comp (Dec (F := ℚ) B).subtype)
    ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)) (r.comp (Dec (F := ℚ) B).subtype)

def FinEnd : Prop :=
  ∃ U : Subgroup (G ℚ Ω), U.FiniteIndex ∧ ∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A],
    (∀ a ∈ maximalIdeal O, algebraMap O A a = 0) → ∀ r : G ℚ Ω →* GG 3 A, OrdPt l η Ψ σ g₁ B r →
      ∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap O A)).charpoly

end Ord

variable {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω)

end UpperTheory.V.Pr

end
