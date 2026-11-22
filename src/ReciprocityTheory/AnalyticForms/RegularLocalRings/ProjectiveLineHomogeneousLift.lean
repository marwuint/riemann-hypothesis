import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify

namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint

noncomputable section

def projLineAffineCoordinate : Fin 2 → OnePoint ℂ → Fin 1 → ℂ :=
  fun i x _ => if i = 0 then x.elim 0 id else x.elim 0 (fun z => z⁻¹)

def projectiveLineSource : Fin 2 → Set (OnePoint ℂ) :=
  fun i => if i = 0 then Set.range ((↑) : ℂ → OnePoint ℂ) else {x | x ≠ ((0 : ℂ) : OnePoint ℂ)}

def homogeneousLift : Fin 2 → (Σ _ : Unit, Fin 2) → MvPolynomial (Fin 1) ℂ :=
  fun i q => if q.2 = i then 1 else X 0

theorem finset_fin_two_eq_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

theorem projectiveLineSource_zero : projectiveLineSource 0 = Set.range ((↑) : ℂ → OnePoint ℂ) := by
  simp [projectiveLineSource]

private theorem onePoint_elim_coe (z a : ℂ) (f : ℂ → ℂ) : (z : OnePoint ℂ).elim a f = f z := rfl

private theorem coe_mem_projectiveLineSource_zero (w : ℂ) : (w : OnePoint ℂ) ∈ projectiveLineSource 0 := by
  rw [projectiveLineSource_zero]
  exact ⟨w, rfl⟩

theorem projectiveLine_mem_conePts_span (z : (Σ _ : Unit, Fin 2) → ℂ) :
    z ∈ conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)) ↔
      (∃ j, z ⟨(), j⟩ ≠ 0) ∧ z ⟨(), 0⟩ = 0 := by
  simp only [conePts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 (), ?_⟩
    have := h2 _ (Ideal.subset_span (Set.mem_singleton _))
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · cases k
      exact h1
    · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      simp [h2]

theorem projection_surjective (z : (Σ _ : Unit, Fin 2) → ℂ)
    (hz : z ∈ conePts (⊥ : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ)))
    (hD : z ∉ conePts (Ideal.span {X ⟨(), 0⟩} : Ideal (MvPolynomial (Σ _ : Unit, Fin 2) ℂ))) :
    ∃ i, ∃ x ∈ projectiveLineSource i, SameOrbit (fun q => eval (projLineAffineCoordinate i x) (homogeneousLift i q)) z := by
  have h1 : ∃ j, z ⟨(), j⟩ ≠ 0 := by
    simp only [conePts, Set.mem_setOf_eq] at hz
    exact hz.1 ()
  have h0 : z ⟨(), 0⟩ ≠ 0 := fun h => hD ((projectiveLine_mem_conePts_span z).mpr ⟨h1, h⟩)
  refine ⟨0, ((z ⟨(), 1⟩ / z ⟨(), 0⟩ : ℂ) : OnePoint ℂ), coe_mem_projectiveLineSource_zero _, ?_⟩
  unfold SameOrbit
  refine ⟨fun _ => (z ⟨(), 0⟩)⁻¹, fun _ => inv_ne_zero h0, ?_⟩
  funext q
  obtain ⟨⟨⟩, k⟩ := q
  obtain rfl | rfl := finset_fin_two_eq_cases k
  · simp [homogeneousLift, h0]
  · simp [homogeneousLift, projLineAffineCoordinate, onePoint_elim_coe] <;> (try field_simp) <;> (try ring)

end

end ReciprocityTheory.AnForm.R
