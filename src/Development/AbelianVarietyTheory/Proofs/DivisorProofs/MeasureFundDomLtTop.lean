import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open scoped NNReal Pointwise
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.UnitaryVol

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero] at h1
  simp at h1

theorem isHermND_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : X.IsHerm σ B r s) : IsHermND σ (X.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, hσ]
    exact (h.herm j i).symm
  · have hJ : X.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply det_ne_zero_of_isCartan (h.cartan w)
      rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]
    rw [show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

end GlobalTheory.UnitaryVol
