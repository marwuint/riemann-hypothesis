import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocLanglands
open scoped Pointwise

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local notation "NK₁[" k ", " m "]" =>
  ((unipB k (Fin m) : Set (GL (Fin m) k)) * (KOne k (Fin m) : Set (GL (Fin m) k)))

section Loc

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]

variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

def phi (m : ℕ) : GL (Fin m) ℤ_[g] →* GL (Fin m) (w.adicCompletion E) :=
  (Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g m)

theorem phi_apply {m : ℕ} (b : GL (Fin m) ℤ_[g]) :
    phi i m b = Matrix.GeneralLinearGroup.map i.toRingHom (inc g m b) := rfl

include hi

end Loc

end DiscreteGroups.sglob.DzRed
