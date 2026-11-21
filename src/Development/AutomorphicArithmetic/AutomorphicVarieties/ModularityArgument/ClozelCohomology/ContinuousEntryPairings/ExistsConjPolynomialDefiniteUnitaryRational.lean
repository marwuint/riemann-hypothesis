import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

private theorem polyConj_coord_pInf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (τ : E →+* ℂ) (x : E) :
    coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by
    first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]
  unfold coord
  split_ifs with hτ
  · simp only [Pi.evalRingHom_apply, h, hτ]
  · rcases InfinitePlace.embedding_mk_eq τ with h' | h'
    · exact absurd h' hτ
    · simp [h, h']

theorem exists_cEmb_entry_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {γ : UA E n}
    (hγ : γ ∈ ratU E n) {k : UA E n} (hk : cInf k = cInf γ) (i j : Fin n) :
    ∃ x : E, ∀ τ : E →+* ℂ, (cEmb τ k).val i j = τ x := by
  obtain ⟨γ₀, h₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine ⟨γ₀.val i j, fun τ => ?_⟩
  have h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j) := rfl
  have h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j) := rfl
  rw [h1, hk, h2, ← h₀]
  exact polyConj_coord_pInf τ _

end GlobalTheory.UnitaryBC
