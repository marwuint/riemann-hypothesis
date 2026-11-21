import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.CardStepOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatLocGlob

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def CofinStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V),
    Submodule.IsLattice E L → Submodule.IsLattice E N →
    ∃ D : ℤ, D ≠ 0 ∧ (∀ v ∈ L, (D : 𝓞 E) • v ∈ N) ∧ (∀ v ∈ N, (D : 𝓞 E) • v ∈ L)

def LocGmapStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (u : V ≃ₗ[E] V) (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V),
    loc (K := E) p (gmap u L) = gmap u (loc (K := E) p L)

end PI.UnitaryGroupMassFormula.UJClassMass

end
