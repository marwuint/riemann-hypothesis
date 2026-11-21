import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem um_countable_HFinIn (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    Countable (HFinIn (AF F) σ J) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  have : Countable (GL (Fin M) E) :=
    Function.Injective.countable (f := fun u : GL (Fin M) E => (u : Matrix (Fin M) (Fin M) E))
      (fun _ _ h => Units.ext h)
  have hx : ∀ x : HFinIn (AF F) σ J, ∃ u : GL (Fin M) E,
      Formalism.UG.bc (inclR (AF F)) u = ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) := by
    intro x
    have h : ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) ∈ HFin (AF F) σ J :=
      Subgroup.mem_subgroupOf.1 x.2
    unfold HFin at h
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 h
    exact ⟨u, hu⟩
  refine Function.Injective.countable (f := fun x => (hx x).choose) ?_
  intro x y hxy
  have h1 := (hx x).choose_spec
  have h2 := (hx y).choose_spec
  simp only at hxy
  rw [hxy] at h1
  exact Subtype.ext (Subtype.ext (h1.symm.trans h2))

instance t2Space_adelic_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))

end Spec

end PI.VolStabSW
