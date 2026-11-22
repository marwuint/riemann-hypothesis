import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalRoots

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem mem_fixingSubgroup_adjoinRoots (m : ℕ) (g : Gal(AlgebraicClosure E/E)) :
    g ∈ (adjoinRoots E m).fixingSubgroup ↔ ∀ ζ : AlgebraicClosure E, ζ ^ m = 1 → g ζ = ζ := by
  constructor
  · intro hg ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg ζ
      (IntermediateField.subset_adjoin E _ hζ)
  · intro h
    have hle : adjoinRoots E m ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro ζ hζ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      have : Subgroup.zpowers g ≤ MulAction.stabilizer Gal(AlgebraicClosure E/E) ζ := by
        rw [Subgroup.zpowers_le]
        exact h ζ hζ
      exact fun f hf => this hf
    exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers g)

private theorem comap_princ_eq [CharZero E] (n : ℕ) :
    (princ l n).comap (eps l E) = (adjoinRoots E (l ^ n)).fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap, eps_mem_princ_iff, mem_fixingSubgroup_adjoinRoots]

theorem card_map_redPow_galImage [CharZero E] (n : ℕ) :
    Nat.card ((galImage l E).map (redPow l n)) = Module.finrank E (adjoinRoots E (l ^ n)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← comap_princ_eq, princ,
    MonoidHom.comap_ker, Subgroup.index_ker, galImage, MonoidHom.map_range]

end KStar.TotallyRealRoots
