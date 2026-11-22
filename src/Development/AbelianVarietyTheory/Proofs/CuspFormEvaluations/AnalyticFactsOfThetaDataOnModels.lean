import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem GlobalTheory.Shares.exists_anFacts_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  intro D T h j hj n N ka wL wF w Tn CR c hka hA hOn hM hTie
  subst hka
  obtain ⟨A⟩ := hA
  obtain ⟨R, e, hR⟩ := _root_.GlobalTheory.Shares.exists_isRdgU D T h j hj n
  obtain ⟨t, ht, ⟨Fl⟩⟩ := _root_.GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj N wL wF w Tn _ A
  classical
  let ι : Type := Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ
  have : Fintype ι := inferInstance
  let en : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let xs : Fin (Fintype.card ι) → R.Y := fun q =>
    e.symm ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩
  have hxs : ∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩ :=
    fun q => e.apply_symm_apply _
  have h1 := _root_.GlobalTheory.Shares.points_and_interp D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn
  refine ⟨R, t, _, xs, ?_, h1.1, h1.2,
    _root_.GlobalTheory.Shares.VanDiv.vanishing_division D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn,
    _root_.GlobalTheory.Shares.LeadDeep.main D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    _root_.GlobalTheory.UpperRecord.upper D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    _root_.GlobalTheory.LowerBound.lower_bound D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs CR c rfl hM,
    _root_.GlobalTheory.Containment.main D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn CR c rfl ?_⟩
  · intro Q hQ
    have hσ : R.σ = T.σ₀ := RingHom.ext hR.1
    rw [hσ]
    exact ht Q hQ
  · exact fun F hF => (hTie F).1 hF
