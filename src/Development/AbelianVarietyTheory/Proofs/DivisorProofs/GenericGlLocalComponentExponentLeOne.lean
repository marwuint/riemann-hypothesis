import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeries

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DetProd

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_isGeneric_of_isLocComp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    {τ : GlobalTheory.CuspRep.CuspSub E n} {w : HeightOneSpectrum (𝓞 E)}
    {ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))} (h : τ.IsLocComp w ρ) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ ρ.ρ := by
  obtain ⟨f, hf0, hf⟩ := h
  let S : Subrepresentation (τ.locRep w) := ⟨LinearMap.range f, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ.ρ g v, hf g v⟩⟩
  have hS : S.toSubmodule ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  obtain ⟨ψ, hc, h1, hg⟩ := GlobalTheory.CuspDetBlocks.exists_isGeneric_subrep τ w S hS
  exact ⟨ψ, hc, h1, hg.of_surjective (σ := S.toRepresentation) ⟨f.rangeRestrict, fun g => LinearMap.ext fun v => by exact Subtype.ext (hf g v)⟩
    (LinearMap.surjective_rangeRestrict _)⟩

end GlobalTheory.ThK.DetProd

end
