import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleOfContra

open ProjLine

section General

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V}

theorem isIrreducible_quot {S : Subrepresentation π} (hS : IsCoatom S) : (quot S).IsIrreducible := by
  have h1 : S.toSubmodule ≠ ⊤ := fun e => hS.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (quot S)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ S.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π := ⟨T.toSubmodule.comap S.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hle : S ≤ T' := fun v hv => by
    show S.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hv]
    exact T.toSubmodule.zero_mem
  rcases hS.le_iff.1 hle with e | e
  · right
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := e ▸ trivial
    exact this
  · left
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := hy
    rw [e] at this
    exact (Submodule.Quotient.mk_eq_zero _).2 this

end General

section GeneralLinearIntegers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem isSmooth_quot (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth (quot S) :=
  (IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ

end GeneralLinearIntegers

end GlobalTheory.CosocleOfContra
