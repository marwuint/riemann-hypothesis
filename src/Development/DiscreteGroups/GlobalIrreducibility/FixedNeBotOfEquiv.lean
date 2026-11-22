import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzGenDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.DiscreteGroups.GlobalIrreducibility.CellVecFixed
import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Place

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

end Place

end DiscreteGroups.sglob.DzType
