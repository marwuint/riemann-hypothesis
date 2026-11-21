import Development.EtaleCohomology.EtaleSheaves.LeafGeoVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSpreadVCut

def LeafCloseB : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧ topologicalKrullDim B ≤ ringKrullDim A

lemma succ_le_of_lt {a x : WithBot ℕ∞} (h : a < x) : a + 1 ≤ x ∧ a + 1 < ⊤ := by
  induction a with
  | bot => exact ⟨by simp, by simp⟩
  | coe n =>
    induction x with
    | bot => exact absurd h (not_lt_bot)
    | coe m =>
      have h' : n < m := WithBot.coe_lt_coe.mp h
      have hn : n ≠ ⊤ := ne_top_of_lt h'
      refine ⟨?_, ?_⟩
      · rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
        exact Order.add_one_le_of_lt h'
      · rw [← WithBot.coe_one, ← WithBot.coe_add]
        exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr (by
          lift n to ℕ using hn
          exact ENat.natCast_ne_top (n + 1)))

end LateralTheory.E.LeafSpreadVCut

end
