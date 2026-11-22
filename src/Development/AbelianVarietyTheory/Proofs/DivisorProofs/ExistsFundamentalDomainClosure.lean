import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.QDom

open scoped Pointwise

end GlobalTheory.QDom

namespace GlobalTheory.QDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem countable_numberField : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  classical
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hmat : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun A : GL (Fin n) E => (A : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hpre : ∀ x : ratU σ J, ∃ A : GL (Fin n) E, Matrix.GeneralLinearGroup.map (inclR (AF F)) A = ((x : UA σ J) : GL (Fin n) (AE F E)) := by
    intro x
    have := x.2
    unfold ratU at this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at this
    exact this
  choose f hf using hpre
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

set_option synthInstance.maxHeartbeats 400000 in
theorem measurable_mul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    Measurable (g * ·) := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  apply Continuous.measurable
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Subgroup.coe_mul, Units.val_mul]
    exact continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_mul continuous_const

end GlobalTheory.QDom

namespace GlobalTheory.QDom

end GlobalTheory.QDom
