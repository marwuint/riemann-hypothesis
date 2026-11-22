import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.LiftC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

end Shape

end UpperTheory.V.Sd
