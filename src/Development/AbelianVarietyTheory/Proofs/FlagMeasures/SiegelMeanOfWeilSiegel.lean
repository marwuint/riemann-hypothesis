import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsOfFixedInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProductStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureGaussian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLattStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedAdditiveCharacterConductor

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Count GlobalTheory.GaussMean
open Formalism.MainNotions.S (AutInst uMat)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SiegelWeilMean

theorem lintegral_eq_of_meanC {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : μ S < ⊤)
    (G : α → ENNReal) (hG : Measurable G) (hfin : ∫⁻ a in S, G a ∂μ < ⊤) (c : ℝ)
    (h : meanC μ S (fun a => ((G a).toReal : ℂ)) = (c : ℂ)) :
    ∫⁻ a in S, G a ∂μ = μ S * ENNReal.ofReal c := by
  by_cases h0 : μ S = 0
  · rw [h0, zero_mul, setLIntegral_measure_zero _ _ h0]
  have h1 : (μ S).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hS.ne⟩
  unfold meanC at h
  beta_reduce at h
  rw [integral_complex_ofReal, integral_toReal hG.aemeasurable (ae_lt_top hG hfin.ne), Complex.real_smul] at h
  have h2 : (μ S).toReal⁻¹ * (∫⁻ a in S, G a ∂μ).toReal = c := by exact_mod_cast h
  rw [← h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin.ne, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_toReal hS.ne, ENNReal.mul_inv_cancel h0 hS.ne, one_mul]

theorem exists_transport (I : AutInst) (T : HA (AF I.F) I.cm.sig I.J ≃ₜ* I.GA)
    (hT : ∀ h, (show HR (AF I.F) I.cm.sig I.J from h) ∈ HFinIn (AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset)
    (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ Measurable T ∧ μ S = I.muA μf fund ∧
      ∀ f : I.GA → ENNReal, ∫⁻ h in S, f (T h) ∂μ = ∫⁻ x in fund, f x ∂(I.muA μf) := by
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by unfold Formalism.REAL.muG; infer_instance
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  haveI : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  haveI : BorelSpace I.GA := inferInstance
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := inferInstance
  obtain ⟨Γ, hΓ, -, -, hF⟩ := GlobalTheory.RatDiscrete.rational_points I
  let e : HA (AF I.F) I.cm.sig I.J ≃ᵐ I.GA := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e ((I.muA μf).map e.symm) (I.muA μf) :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hmem : ∀ g : Γ, (show HR (AF I.F) I.cm.sig I.J from T.symm g) ∈ HFinIn (AF I.F) I.cm.sig I.J := fun g => by
    refine (hT (T.symm g)).2 ?_
    have : T (T.symm g) = g := T.apply_symm_apply _
    exact this.symm ▸ (hΓ ▸ g.2 : g.1 ∈ I.GFset)
  refine ⟨(I.muA μf).map e.symm, e ⁻¹' fund, T.symm.isHaarMeasure_map _, ?_, e.measurable,
    hp.measure_preimage_equiv _, fun f => hp.setLIntegral_comp_preimage_emb e.measurableEmbedding f _⟩
  refine (hF μf fund hfund).preimage_of_equiv hp.quasiMeasurePreserving
    (e := fun g => ⟨T.symm g, hmem g⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun g x => ?_
  · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
  · exact ⟨⟨T b.1, by rw [← SetLike.mem_coe, hΓ]; exact (hT _).1 b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
  · change T (T.symm g * x) = g * T x
    rw [map_mul, T.apply_symm_apply]

theorem const_eq {ι κ : Type} [Fintype κ] (q : ι → ℝ) (hq : ∀ u, 0 < q u) (m : ι → ℤ)
    (hm : (Function.support m).Finite) (a : ι → ℝ) (Lv : ℝ) (ha : HasProd a Lv⁻¹) (lam g : κ → ℝ)
    (hlam : ∀ v, lam v ≠ 0) (w : ℝ) (hw : 0 < w) (n f : ℕ) (hf : Fintype.card κ = f)
    (hp : ∏ᶠ u, q u ^ m u = (2 * w) ^ f * ∏ v, |lam v|) :
    ((∏ v, 2 ^ n * |lam v| ^ ((n : ℝ) - 1 / 2) * g v : ℝ) : ℂ) *
      ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) =
      (((2 * w) ^ ((f : ℝ) / 2) * (w ^ (n * f))⁻¹ / Lv * ∏ v, g v : ℝ) : ℂ) := by
  have hout : ∀ u ∉ hm.toFinset, m u = 0 := fun u hu => by simpa using hu
  have h1 : HasProd (fun u => (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)))
      (∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ))) :=
    hasProd_prod_of_ne_finset_one fun u hu => by simp [hout u hu]
  have h2 : ∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) =
      ((2 * w) ^ f * ∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) := by
    rw [Real.finset_prod_rpow _ _ fun u _ => (zpow_pos (hq u) _).le, ← hp,
      finprod_eq_prod_of_mulSupport_subset _ (s := hm.toFinset)]
    intro u hu
    by_contra h
    exact hu (by simp [hout u h])
  have h3 := (h1.mul ha).map Complex.ofRealHom Complex.continuous_ofReal
  have h4 : ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) = _ := h3.tprod_eq
  rw [h4, h2, Complex.ofRealHom_eq_coe, ← Complex.ofReal_mul]
  congr 1
  have hl : 0 < ∏ v, |lam v| := Finset.prod_pos fun v _ => abs_pos.2 (hlam v)
  have h5 : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) * (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = 1 := by
    rw [← Real.rpow_add hl]; simp
  have h6 : ((2 * w) ^ f) ^ ((1 / 2 : ℝ) - (n : ℝ)) = (2 * w) ^ ((f : ℝ) / 2) * ((2 * w) ^ (n * f))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (2 * w) (n * f),
      ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
    congr 1; push_cast; ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf,
    Real.finset_prod_rpow _ _ fun v _ => abs_nonneg _, Real.mul_rpow (by positivity) hl.le, h6, mul_pow, pow_mul 2]
  have : (2 ^ n : ℝ) ^ f ≠ 0 := by positivity
  have h7 : (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = ((∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2))⁻¹ :=
    eq_inv_of_mul_eq_one_right h5
  have : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) ≠ 0 := by positivity
  rw [h7]
  field_simp

end GlobalTheory.SiegelWeilMean
