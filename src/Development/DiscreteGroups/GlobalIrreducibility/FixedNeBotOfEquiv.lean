import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzGenDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.DiscreteGroups.GlobalIrreducibility.CellVecFixed
import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isLower_iff {g m : ℕ} [Fact g.Prime] (b : Gn g m) :
    IsLower b ↔ (b : Mt g m).BlockTriangular OrderDual.toDual := Iff.rfl

section Place

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem lowS_apply {m : ℕ} (x : GL (Fin m) ℤ_[g]) (a b : Fin m) :
    ((((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m)) x : GL (Fin m) (w.adicCompletion E)) :
      Matrix (Fin m) (Fin m) (w.adicCompletion E)) a b = i ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a b : ℚ_[g]) := rfl

include hi

end Place

end DiscreteGroups.sglob.DzType
