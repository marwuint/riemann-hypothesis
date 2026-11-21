import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bridge

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.Aut

def IsQi (K : Type) [Field K] [NumberField K] : Prop := Module.finrank ℚ K = 2 ∧ ∃ i : K, i * i = -1

structure BPrime (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : Af.AutOn K ι (-1) a

end UpperTheory.V.Aut

end
