import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjective

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CycPair

theorem cInfAt_log_nsq_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec) (δ : ℝ), 0 < δ → ∀ y, CInfAt (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) y := by
  intro k _ X p σ M s δ hδ y
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := (_root_.GlobalTheory.Mix.SecNorm.logSec_basic k X p σ M s).2.2.1 y
  refine ⟨W, ι, inferInstance, g, fun w => Real.log (F w + δ), O ∩ F ⁻¹' Set.Ioi (-δ), h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, ?_⟩, ?_, ?_⟩
  · have h0 := M.φ.nsq_nonneg (secVal p σ s) y
    rw [h₅.eq_of_nhds] at h0
    exact lt_of_lt_of_le (neg_neg_of_pos hδ) h0
  · refine ((h₄.mono Set.inter_subset_left).add contDiffOn_const).log fun w hw => ?_
    have : -δ < F w := hw.2
    linarith
  · filter_upwards [h₅] with z hz
    rw [hz]

theorem int_cons_addFn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (f : CxPts p σ → ℝ), Intg (Fin.cons A L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f ∧ Mix.int (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f = Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) f + Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f := by
  intro k _ X p σ hp e L A u hu f hA hU
  have hc := _root_.GlobalTheory.Mix.isom_calculus k X X p p σ (𝟙 X) (Category.id_comp p)
  have hpart := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k X p σ hp (e + 1) (Fin.cons (A.addFn u hu) L)
    (Fin.cons (A.tens (MLine.ofFun u hu)) L) (Fin.cases (hc.2.2.2.2.1 A u hu) fun i => hc.1 (L i))
  have h := _root_.GlobalTheory.Mix.int_update_tens k X p σ hp (e + 1) (Fin.cons A L) 0 A (MLine.ofFun u hu) f
  simp only [Fin.update_cons_zero] at h
  have h' := h hA hU
  rw [← h'.2]
  have h1 := h'.1
  simp only [Intg, Mix.int, hpart] at h1 ⊢
  exact ⟨h1, trivial⟩

theorem int_logSec_le : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → ∀ (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → ∀ δ : ℝ, 0 < δ → Intg L (M.logSec s) → Intg L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) → Mix.int L (M.logSec s) ≤ Mix.int L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) / 2 := by
  intro F _ X _ p σ hp D L hL M s hs δ hδ h₁ h₂
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have hneg := _root_.GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg F X p σ D L hL
  have hnull := _root_.GlobalTheory.MixNull.part_compl_null F X p σ σ.injective hp D L 1 _ hs
  have hpos := (_root_.GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).2.1
  simp only [Mix.int, hneg, integral_zero_measure, sub_zero]
  rw [← integral_div]
  refine integral_mono_ae h₁.1 (h₂.1.div_const 2) ?_
  have hae : ∀ᵐ y ∂part L 1, y ∈ ptsIn p σ (nonzeroLocus s) := hnull
  filter_upwards [hae] with y hy
  have h0 := (hpos y).2 hy
  have := Real.log_le_log h0 (le_add_of_nonneg_right hδ.le)
  simp only [MLine.logSec]
  linarith

theorem mem_of_mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A : LB X} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (U : X.Opens) (h : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ U) (z : X) (hz : (divOfSec hA s hs).mult z ≠ 0) : z ∈ U :=
  (h z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)).resolve_left fun h' =>
    notMem_supp_divOfSec.2 h' (CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem side_le : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → N.φ.SemiPosReg (e + 1) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) ≤ side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod hL hN
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  let v : ℕ → CxPts p σ → ℝ := fun n y => Real.log (N.φ.nsq (secVal p σ t) y + δ n)
  let u : ℕ → CxPts p σ → ℝ := fun m y => Real.log (M.φ.nsq (secVal p σ s) y + δ m)
  have hv : ∀ n y, CInfAt (v n) y := fun n => cInfAt_log_nsq_add F X p σ N t (δ n) (hδ n)
  have hu : ∀ m y, CInfAt (u m) y := fun m => cInfAt_log_nsq_add F X p σ M s (δ m) (hδ m)
  have cu : ∀ m, Continuous (u m) := fun m => continuous_iff_continuousAt.2 fun y => (hu m y).continuousAt
  have fin : ∀ (L' : Fin (e + 1) → MLine p σ) (f : CxPts p σ → ℝ), Continuous f → Intg L' f :=
    fun L' => (_root_.GlobalTheory.MixFin.finite_and_intg hP F X p σ (e + 1) hproj hdim L').2
  have lint : ∀ L' : Fin (e + 1) → MLine p σ, Intg L' (M.logSec s) :=
    fun L' => _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim L' M s hs
  have supS : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t :=
    mem_of_mult_divOfSec_ne_zero M.φ.isLB s hs _ hcod
  have supT : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s :=
    mem_of_mult_divOfSec_ne_zero N.φ.isLB t ht _ fun z hz => (hcod z hz).symm
  have key : ∀ m n, Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
      + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) ≤
      (Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m)
        + Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n)) / 2 := by
    intro m n
    obtain ⟨-, h1⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (M.logSec s) (lint _) (lint _)
    obtain ⟨-, h2⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (u m) (fin _ _ (cu m)) (fin _ _ (cu m))
    have hsp : ∀ i, ((Fin.cons (N.addFn (v n) (hv n)) L : Fin (e + 1) → MLine p σ) i).φ.SemiPosReg (e + 1) :=
      Fin.cases (_root_.GlobalTheory.Mix.semiPosReg_addFn_log_nsq F X p σ (e + 1) N hN t (δ n) (hδ n)).2 hL
    have h3 := int_logSec_le F X p σ hproj (e + 1) _ hsp M s hs (δ m) (hδ m) (lint _) (fin _ _ (cu m))
    have h4 := _root_.GlobalTheory.Mix.int_cons_ofFun_symm hP F X p σ e hproj hdim L (v n) (u m) (hv n) (hu m)
    rw [← h1]
    refine h3.trans (le_of_eq ?_)
    change Mix.int _ (u m) / 2 = _
    rw [h2, h4]
  have ps : ∀ n, 2 * Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
        - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n) :=
    fun n => _root_.GlobalTheory.poincareLelong_sec hP F X p σ e hproj hdim L M s hs (v n) (hv n)
  have pt : ∀ m, 2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z
        - Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m) :=
    fun m => _root_.GlobalTheory.poincareLelong_sec hP F X p σ e hproj hdim L N t ht (u m) (hu m)
  have limT := _root_.GlobalTheory.Mix.tendsto_logReg hP F X p σ e hproj hdim N t
  have limS := _root_.GlobalTheory.Mix.tendsto_logReg hP F X p σ e hproj hdim M s
  have l1 : Tendsto (fun n => ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z)) :=
    limT.2 L _ supS
  have l2 : Tendsto (fun n => Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) atTop
      (𝓝 (2 * Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := limT.1 ht _
  have l3 : ∀ m, Tendsto (fun n => Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n))
      atTop (𝓝 (2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t))) :=
    fun m => limT.1 ht _
  have l4 : Tendsto (fun m => ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z)) :=
    limS.2 L _ supT
  have step : ∀ m, side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
      - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) ≤
      (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) / 2 := by
    intro m
    have lim1 : Tendsto (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
        + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) atTop
        (𝓝 (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
          - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := by
      have e1 : (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
          + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) =
          fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
            + (∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
              - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) / 2 :=
        funext fun n => by rw [← ps n]; ring
      rw [e1]
      convert tendsto_const_nhds.add ((l1.sub l2).div_const 2) using 2
      simp only [side]
      ring
    have lim2 := (tendsto_const_nhds (x := Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m))).add (l3 m)
    have h := le_of_tendsto_of_tendsto' lim1 (lim2.div_const 2) (key m)
    have := pt m
    linarith
  have h := ge_of_tendsto' (l4.div_const 2) step
  simp only [side] at h ⊢
  linarith

end GlobalTheory.CycPair
