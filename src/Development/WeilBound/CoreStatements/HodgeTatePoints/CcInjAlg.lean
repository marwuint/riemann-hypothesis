import Development.WeilBound.CoreStatements.HodgeTatePoints.MapFirstPower

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

theorem mulVec_injective_map_iff {k k₂ m n : Type} [Field k] [Field k₂] [Fintype m] [Fintype n] (f : k →+* k₂)
    (M : Matrix m n k) : Function.Injective (M.map f).mulVec ↔ Function.Injective M.mulVec := by
  letI := f.toAlgebra
  rw [Matrix.mulVec_injective_iff, Matrix.mulVec_injective_iff]
  exact linearIndependent_algebraMap_comp_iff (R := k) (S := k₂) (v := M.col)

theorem conjInj_iff_fromRows {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (p : ℕ) : ConjInj B p ↔ Function.Injective (Matrix.fromRows (hw B p) (am B p).transpose).mulVec := by
  have e : (Matrix.fromRows (hw B p) (am B p).transpose).mulVec =
      (Equiv.sumArrowEquivProdArrow (Fin d) (Fin d) R).symm ∘ alpha B p := by
    funext u
    rw [Matrix.fromRows_mulVec, Function.comp_apply, alpha_apply]
    rfl
  rw [e, Equiv.comp_injective, ConjInj]

theorem conjInj_map {k k₂ : Type} [Field k] [Field k₂] {f : k →+* k₂} {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {B : FB k d O} {B₂ : FB k₂ d O} (h : IsMapOf f B B₂) (p : ℕ) : ConjInj B₂ p ↔ ConjInj B p := by
  obtain ⟨h1, h2⟩ := (map_mats k k₂ f d O B B₂ h).2.2 p
  rw [conjInj_iff_fromRows, conjInj_iff_fromRows, ← mulVec_injective_map_iff f, h1, h2, Matrix.fromRows_map,
    Matrix.transpose_map]

end PositivityTheory.HtPt.Cc
