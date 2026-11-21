import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFlagInCellOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBaseFormFlagCellCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFirstChernFormsPullbackCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartComplComplexPointsInOpenEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagona
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartEqLintegralImageInjectiveHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.LocFib

theorem continuousOn_dens {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α)
    (i : A.ι) : ContinuousOn (fun v => (dens (A.loc α i v)).re) (A.e i).target :=
  Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)

set_option maxHeartbeats 800000 in

theorem part_preimage : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).IsForm ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) → ∀ (s : ℤˣ) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (O : Set (CxPts X.str σ)), IsOpen O → O ⊆ c.e.source → (∀ x ∈ O, A ∈ E.S (under x)) → ∀ T, MeasurableSet T → T ⊆ O → (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s (ptMap σ f hf ⁻¹' T) = (atlas X σ).part α s T := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα hβ s c A O hO hOc hOA T hT hTO
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  haveI : T2Space (CxPts X.str σ) := CxPts.t2Space _ _
  haveI : T2Space (CxPts Y.str σ) := CxPts.t2Space _ _
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint F X Y ι m E E' φ f hR _ A (hOA x₀ (hTO hx₀))
  have hdim := _root_.GlobalTheory.FlagCell2.Dim.main F σ X Y ι m E E' φ f hf hR
  let ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m := Fintype.equivOfCardEq (by simp [hdim])
  obtain ⟨hopen, hinj, himg⟩ := _root_.GlobalTheory.FlagCell2.cellMap_image_eq F σ X Y ι m E E' φ f hf hR c A u hu _ ε
  have hW := (_root_.GlobalTheory.FlagCell2.isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).1
  have hπ : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
  have hTm : MeasurableSet (ptMap σ f hf ⁻¹' T) := hπ.measurable hT
  have hnull := _root_.GlobalTheory.FlagCell2Null.part_compl_ptsIn F σ Y ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) ⟨_, hW⟩ hu s
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s := ⟨_, rfl⟩
  rw [← hμ] at hnull ⊢
  have h1 : μ (ptMap σ f hf ⁻¹' T) = μ (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) := by
    refine (measure_inter_add_diff (ptMap σ f hf ⁻¹' T) hopen.measurableSet).symm.trans ?_
    have h0 : μ (ptMap σ f hf ⁻¹' T \ cellSet E E' φ f hf c A u) = 0 :=
      by
      refine measure_mono_null (fun y hy => ?_) hnull
      intro hy'
      have h2 : under y ∈ (⟨_, hW⟩ : Y.X.Opens) := mem_ptsIn.1 hy'
      have h3 : InCell E E' φ f A u (under y) := h2
      exact hy.2 ⟨h3, hOc (hTO hy.1)⟩
    rw [h0, add_zero]
  have hmet := _root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH)
  have hG : ∀ v ∈ c.e '' O, ∀ τ, MContDiffAt ∞ (fun w => H A (c.e.symm w) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    rintro _ ⟨x, hx, rfl⟩ τ
    exact ((hmet x A (hOA x hx) τ).2 c (hOc hx)).self_of_nhds
  have hOo : IsOpen (c.e '' O) := c.e.isOpen_image_of_subset_source hO hOc
  have hTi : MeasurableSet (c.e '' T) := by
    have e : c.e '' T = Subtype.val '' (c.e.target.restrict c.e.symm ⁻¹' T) := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨_, c.e.map_source (hOc (hTO hx))⟩, by
          show c.e.symm (c.e x) ∈ T
          rwa [c.e.left_inv (hOc (hTO hx))], rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨_, hv, c.e.right_inv v.2⟩
    rw [e]
    exact (MeasurableEmbedding.subtype_coe c.e.open_target.measurableSet).measurableSet_image.2
      ((continuousOn_iff_continuous_restrict.1 c.e.continuousOn_symm).measurable hT)
  rw [h1, hμ, _root_.GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image _ _ (atlas Y σ) _ hβ _ (cellMap ε f hf c u)
    (cellForm ε (fun v => H A (c.e.symm v)) ((atlas X σ).loc α c)) hopen hinj ?_ s _
    (hTm.inter hopen.measurableSet) Set.inter_subset_right, himg T (hTO.trans hOc) fun x hx => hOA x (hTO hx),
    show (atlas X σ).part α s T = ∫⁻ v in c.e '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re)
      from _root_.GlobalTheory.FlagCell2.part_subset_chart _ _ (atlas X σ) α hα s c T hT (hTO.trans hOc),
    ← _root_.GlobalTheory.FlagCell2.setLIntegral_fibDens ι m _ _ ε (fun v => H A (c.e.symm v))
      (fun v => ((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re) (c.e '' O) (c.e '' T) hOo hTi (Set.image_mono hTO)
      (continuousOn_const.mul ((continuousOn_dens _ hα c).mono ?_))
      (fun τ i j v hv => ((hG v hv τ).1 i j).continuousAt.continuousWithinAt) fun v hv τ => (hG v hv τ).2]
  · refine setLIntegral_congr_fun ((bsL ε).continuous.measurable hTi) fun w hw => ?_
    have hw' := Set.image_mono hTO hw
    beta_reduce
    rw [_root_.GlobalTheory.FlagCell2.CellDens.dens_cellForm ι m _ _ ε _ _ w (fun τ => (hG _ hw' τ).2) fun τ => (hG _ hw' τ).1.of_le (by norm_cast),
      Complex.re_mul_ofReal, mul_assoc]
  · rintro _ ⟨x, hx, rfl⟩
    exact c.e.map_source (hOc hx)
  · intro x hx
    refine ⟨(_root_.GlobalTheory.FlagCell2.cellMap_contDiffAt F σ X Y ι m E E' φ f hf hR c A u _ ε x hx).differentiableAt two_ne_zero, ?_⟩
    rw [Pi.mul_apply, cellForm, map_mul, _root_.GlobalTheory.FlagCell2.pullback_cell F σ X Y ι m E E' φ f hf hR c A u _ ε α hα x hx]
    congr 1
    exact _root_.GlobalTheory.FlagCell2.pull_aeval_even _ _ _ _ _ _ _ (_root_.GlobalTheory.FlagCell2.GradedPull.grF_eq_pull F σ X Y ι m E E' φ f hf hR c A u H hH ε x hx)

end GlobalTheory.FlagCell2.LocFib
