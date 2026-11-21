import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfCechDisjointCover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_iso {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') [IsIso f] :
    Conn R F c f := by
  have hb : ∀ n, Function.Bijective (pull R f F n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
      fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
      fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩
  exact fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩

private theorem conn_congr {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U U' : X.Opens} (e : U = U')
    (h : Conn R F c (sch.map U.ι)) : Conn R F c (sch.map U'.ι) := e ▸ h

private theorem conn_top {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} {U : X.Opens} (e : U = ⊤) :
    Conn R F c (sch.map U.ι) := by
  subst e
  haveI : IsIso (⊤ : X.Opens).ι := by
    first
      | infer_instance
      | (rw [← Scheme.topIso_hom]; infer_instance)
      | exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact conn_iso F c _

private theorem exists_good {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U : X.Opens}
    (H : ∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι))
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ∃ (O : Scheme.{0}) (o : O ⟶ Y) (_ : IsOpenImmersion o), y ∈ Set.range o ∧
      Conn R F c (sch.map ((o ≫ j) ⁻¹ᵁ U).ι) := by
  by_cases hy : j y ∈ U
  · refine ⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hy
    · rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _
  · obtain ⟨Y', j', hj', hx, hsub, hC⟩ := H (j y) hy j.opensRange ⟨y, rfl⟩
    have hle : Set.range j' ⊆ Set.range j := hsub
    have hfac : IsOpenImmersion.lift j j' hle ≫ j = j' := IsOpenImmersion.lift_fac j j' hle
    haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'
    refine ⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hx
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hfac]
    · rw [hfac]
      exact hC

end
