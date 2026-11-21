import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianRapidDecay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.RealDensity

theorem selfDual_map {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V]
    [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [IsTopologicalAddGroup V']
    (T : V ≃ₜ+ V') {μ : Measure V} {χ : V → V → ℂ} {χ' : V' → V' → ℂ} (h : SelfDual μ χ)
    (hχ : ∀ x y, χ x y = χ' (T x) (T y)) : SelfDual (μ.map T) χ' := by
  have hemb : Topology.IsClosedEmbedding T := T.toHomeomorph.isClosedEmbedding
  have hme : MeasurableEmbedding T := hemb.measurableEmbedding
  have : μ.IsAddHaarMeasure := h.1
  refine ⟨inferInstance, ?_⟩
  intro Φ hΦc hΦs hint z

  have hin : (fun y => ∫ x, Φ x * χ' x y ∂(μ.map T)) ∘ T =
      fun y => ∫ x, Φ (T x) * χ x y ∂μ := by
    funext y
    simp only [Function.comp_apply]
    rw [hemb.integral_map]
    simp only [hχ]
  have hint' : Integrable (fun y => ∫ x, Φ (T x) * χ x y ∂μ) μ := by
    rw [← hin, ← hme.integrable_map_iff]
    exact hint
  have hc : Continuous (fun x => Φ (T x)) := hΦc.comp T.continuous
  have hs : HasCompactSupport (fun x => Φ (T x)) := hΦs.comp_homeomorph T.toHomeomorph
  have key := h.2 (fun x => Φ (T x)) hc hs hint' (T.symm z)
  rw [hemb.integral_map]
  have hz : z = T (T.symm z) := (T.apply_symm_apply z).symm
  calc ∫ y, (∫ x, Φ x * χ' x (T y) ∂(μ.map T)) * χ' (T y) z ∂μ
      = ∫ y, (∫ x, Φ (T x) * χ x y ∂μ) * χ y (T.symm z) ∂μ := by
        congr 1
        funext y
        have := congrFun hin y
        simp only [Function.comp_apply] at this
        rw [this, hz, ← hχ, T.symm_apply_apply]
    _ = Φ (T (-(T.symm z))) := key
    _ = Φ (-z) := by rw [map_neg, T.apply_symm_apply]

theorem exists_coord_base : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∃ a : Ainf I.F ≃ₜ+ (InfinitePlace I.F → ℝ), ∀ x v, θ v (x ⊗ₜ[I.F] (1 : I.E)) = ((a x v : ℝ) : ℂ) := by
  intro I θ hθ
  have hRe : ∀ v : InfinitePlace I.F, v.IsReal := fun v =>
    (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1.1.isReal v

  let e : Ainf I.F ≃+* (InfinitePlace I.F → ℝ) :=
    RingEquiv.piCongrRight fun v => InfinitePlace.Completion.ringEquivRealOfIsReal (hRe v)
  have hec : Continuous e := continuous_pi fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hRe v)).continuous.comp
      (continuous_apply v)
  have hesc : Continuous e.symm := continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hRe v)).symm.continuous.comp
      (continuous_apply v)
  refine ⟨{ toAddEquiv := e.toAddEquiv, continuous_toFun := hec, continuous_invFun := hesc }, ?_⟩
  intro x v

  have hfun : (fun y : Ainf I.F => θ v (y ⊗ₜ[I.F] (1 : I.E))) =
      fun y => InfinitePlace.Completion.extensionEmbedding v (y v) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer (hθ v).2
      ((InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)) ?_
    funext a
    simp only [Function.comp_apply, InfiniteAdeleRing.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
      (hθ v).1, I.φ_over]
    exact (InfinitePlace.Completion.extensionEmbedding_coe v _).symm
  have hx := congrFun hfun x
  change θ v (x ⊗ₜ[I.F] (1 : I.E)) =
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (hRe v) (x v) : ℝ) : ℂ)
  rw [hx, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

private theorem exists_coord_homeomorph_tensor (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ))
    (hθ : ∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) :
    ∃ Ψ : (Ainf I.F ⊗[I.F] I.E) ≃ₜ+ (InfinitePlace I.F → ℂ), ∀ z v, Ψ z v = θ v z := by
  obtain ⟨a, ha⟩ := exists_coord_base I θ hθ
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) I.F I.E) := ⟨Module.finBasisOfFinrankEq I.F I.E I.cm.deg2⟩
  let B : Module.Basis (Fin 2) (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) := Algebra.TensorProduct.basis (Ainf I.F) b
  have hBk : ∀ k, B k = (1 : Ainf I.F) ⊗ₜ[I.F] b k := fun k => Algebra.TensorProduct.basis_apply b k
  have : IsModuleTopology (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf I.F ⊗[I.F] I.E) := IsModuleTopology.toContinuousAdd (Ainf I.F) (Ainf I.F ⊗[I.F] I.E)
  have hcE : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  have hcEs : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap

  have hsum : ∀ z v, θ v z = ∑ k, ((a (B.equivFun z k) v : ℝ) : ℂ) * I.φ v (b k) := by
    intro z v
    conv_lhs => rw [← B.sum_equivFun z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hBk, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← ha, ← (hθ v).1 (b k), ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  have hD : ∀ v, (I.φ v (b 0) * (starRingEnd ℂ) (I.φ v (b 1))).im ≠ 0 := by
    intro v hzero
    have h0 : b 0 ≠ 0 := b.ne_zero 0
    have hφ0 : I.φ v (b 0) ≠ 0 := (map_ne_zero (I.φ v)).2 h0
    have hφ0' : (starRingEnd ℂ) (I.φ v (b 0)) ≠ 0 := (map_ne_zero _).2 hφ0
    have hreal : (starRingEnd ℂ) (I.φ v (b 1 / b 0)) = I.φ v (b 1 / b 0) := by
      rw [map_div₀, map_div₀, div_eq_div_iff hφ0' hφ0]
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hzero ⊢ <;>
        linarith
    have hfix : I.cm.sig (b 1 / b 0) = b 1 / b 0 :=
      (I.φ v).injective (by rw [hcm.2.2.2, ← starRingEnd_apply, hreal])
    obtain ⟨f, hf⟩ := (I.cm.fixed (b 1 / b 0)).1 hfix
    have hx : b 1 = f • b 0 := by
      rw [Algebra.smul_def, hf, div_mul_cancel₀ _ h0]
    have := congrArg (fun z => b.repr z 1) hx
    simp [Module.Basis.repr_self] at this
  have hD' : ∀ v, (I.φ v (b 1) * (starRingEnd ℂ) (I.φ v (b 0))).im ≠ 0 := by
    intro v h
    apply hD v
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h ⊢
    linarith

  let t : Fin 2 → InfinitePlace I.F → ℂ → ℝ := fun k v w =>
    (w * (starRingEnd ℂ) (I.φ v (b (k + 1)))).im /
      (I.φ v (b k) * (starRingEnd ℂ) (I.φ v (b (k + 1)))).im
  have ht0 : ∀ v w, t 0 v w = (w * (starRingEnd ℂ) (I.φ v (b 1))).im /
      (I.φ v (b 0) * (starRingEnd ℂ) (I.φ v (b 1))).im := fun v w => rfl
  have ht1 : ∀ v w, t 1 v w = (w * (starRingEnd ℂ) (I.φ v (b 0))).im /
      (I.φ v (b 1) * (starRingEnd ℂ) (I.φ v (b 0))).im := fun v w => rfl
  have hnz : ∀ v, -((I.φ v (b 0)).re * (I.φ v (b 1)).im) + (I.φ v (b 0)).im * (I.φ v (b 1)).re ≠ 0 ∧
      -((I.φ v (b 1)).re * (I.φ v (b 0)).im) + (I.φ v (b 1)).im * (I.φ v (b 0)).re ≠ 0 := by
    intro v
    have h0 := hD v
    have h1 := hD' v
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0 h1
    constructor
    · intro h; apply h0; linarith
    · intro h; apply h1; linarith
  have ht : ∀ v (r : Fin 2 → ℝ) k,
      t k v (∑ j, ((r j : ℝ) : ℂ) * I.φ v (b j)) = r k := by
    intro v r k
    obtain ⟨h0, h1⟩ := hnz v
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with rfl | rfl
    · rw [ht0, div_eq_iff (hD v), Fin.sum_univ_two]
      simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      ring
    · rw [ht1, div_eq_iff (hD' v), Fin.sum_univ_two]
      simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      ring
  have ht' : ∀ v (w : ℂ), ∑ j, ((t j v w : ℝ) : ℂ) * I.φ v (b j) = w := by
    intro v w
    have e0 : t 0 v w * (I.φ v (b 0) * (starRingEnd ℂ) (I.φ v (b 1))).im =
        (w * (starRingEnd ℂ) (I.φ v (b 1))).im := by rw [ht0, div_mul_cancel₀ _ (hD v)]
    have e1 : t 1 v w * (I.φ v (b 1) * (starRingEnd ℂ) (I.φ v (b 0))).im =
        (w * (starRingEnd ℂ) (I.φ v (b 0))).im := by rw [ht1, div_mul_cancel₀ _ (hD' v)]
    have hD0 := hD v
    rw [Fin.sum_univ_two]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at e0 e1 hD0
    apply Complex.ext <;>
      simp only [Complex.add_im, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] <;>
      apply mul_left_cancel₀ hD0
    · linear_combination (I.φ v (b 0)).re * e0 - (I.φ v (b 1)).re * e1
    · linear_combination (I.φ v (b 0)).im * e0 - (I.φ v (b 1)).im * e1
  refine ⟨{ toFun := fun z v => θ v z
            invFun := fun w => B.equivFun.symm (fun k => a.symm (fun v => t k v (w v)))
            left_inv := ?_
            right_inv := ?_
            map_add' := fun z z' => funext fun v => map_add (θ v) z z'
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun z v => rfl⟩
  · intro z
    apply B.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    rw [a.symm_apply_eq]
    funext v
    change t k v (θ v z) = a (B.equivFun z k) v
    rw [hsum z v]
    exact ht v (fun j => a (B.equivFun z j) v) k
  · intro w
    funext v
    change θ v (B.equivFun.symm (fun k => a.symm (fun v' => t k v' (w v')))) = w v
    rw [hsum, LinearEquiv.apply_symm_apply]
    simp only [a.apply_symm_apply]
    exact ht' v (w v)
  · refine continuous_pi fun v => ?_
    have : (fun z => θ v z) = fun z => ∑ k, ((a (B.equivFun z k) v : ℝ) : ℂ) * I.φ v (b k) :=
      funext fun z => hsum z v
    show Continuous (fun z => θ v z)
    rw [this]
    exact continuous_finsetSum _ fun k _ => (Complex.continuous_ofReal.comp ((continuous_apply v).comp
      (a.continuous.comp ((continuous_apply k).comp hcE)))).mul continuous_const
  · exact hcEs.comp (continuous_pi fun k => a.symm.continuous.comp (continuous_pi fun v =>
      ((Complex.continuous_im.comp ((continuous_apply v).mul continuous_const)).div_const _)))

theorem exists_coord_space : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∃ T : (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) ≃ₜ+ (InfinitePlace I.F → Fin I.n → ℂ), ∀ X v, T X v = (I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i) := by
  intro I θ hθ
  obtain ⟨Ψ, hΨ⟩ := exists_coord_homeomorph_tensor I θ hθ
  have hPu : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hinv : ∀ v (u : Fin I.n → ℂ), I.P v *ᵥ ((I.P v)⁻¹ *ᵥ u) = u := fun v u => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mulVec]
  have hinv' : ∀ v (u : Fin I.n → ℂ), (I.P v)⁻¹ *ᵥ (I.P v *ᵥ u) = u := fun v u => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hPu v), Matrix.one_mulVec]
  refine ⟨{ toFun := fun X v => (I.P v)⁻¹ *ᵥ fun i => Ψ (X 0 i) v
            invFun := fun Y _ i => Ψ.symm (fun v => (I.P v *ᵥ Y v) i)
            left_inv := ?_
            right_inv := ?_
            map_add' := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, ?_⟩
  · intro X
    funext o i
    have ho : o = 0 := Subsingleton.elim o 0
    subst ho
    simp only [hinv]
    exact Ψ.symm_apply_apply (X 0 i)
  · intro Y
    funext v
    simp only [Ψ.apply_symm_apply]
    exact hinv' v (Y v)
  · intro X Y
    funext v
    change (I.P v)⁻¹ *ᵥ _ = (I.P v)⁻¹ *ᵥ _ + (I.P v)⁻¹ *ᵥ _
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [map_add]
  · exact continuous_pi fun v => Continuous.matrix_mulVec continuous_const (continuous_pi fun i =>
      (continuous_apply v).comp (Ψ.continuous.comp ((continuous_apply i).comp (continuous_apply 0))))
  · exact continuous_pi fun _ => continuous_pi fun i => Ψ.symm.continuous.comp (continuous_pi fun v =>
      (continuous_apply i).comp (Continuous.matrix_mulVec continuous_const (continuous_apply v)))
  · intro X v
    change (I.P v)⁻¹ *ᵥ (fun i => Ψ (X 0 i) v) = _
    simp only [hΨ]

private theorem tmul_one_conj_real (I : AutInst) (v : InfinitePlace I.F) (θ : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ) (r : Ainf I.F) :
    (starRingEnd ℂ) (θ (r ⊗ₜ[I.F] (1 : I.E))) = θ (r ⊗ₜ[I.F] (1 : I.E)) := by
  have hRe : v.IsReal := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1.1.isReal v
  have hfun : (fun y : Ainf I.F => θ (y ⊗ₜ[I.F] (1 : I.E))) =
      fun y => InfinitePlace.Completion.extensionEmbedding v (y v) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hθ.2
      ((InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)) ?_
    funext a
    simp only [Function.comp_apply, InfiniteAdeleRing.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
      hθ.1, I.φ_over]
    exact (InfinitePlace.Completion.extensionEmbedding_coe v _).symm
  have hx := congrFun hfun r
  rw [hx, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hRe, Complex.conj_ofReal]

private theorem algebraMap_trace_eq_add_sig (I : AutInst) (e : I.E) :
    algebraMap I.F I.E (Algebra.trace I.F I.E e) = e + I.cm.sig e := by
  classical
  have : Algebra.IsQuadraticExtension I.F I.E := { finrank_eq_two' := I.cm.deg2 }
  let τ : I.E ≃ₐ[I.F] I.E := AlgEquiv.ofAlgHom I.cm.sig I.cm.sig
    (AlgHom.ext fun a => star_star a) (AlgHom.ext fun a => star_star a)
  have hτ : τ ≠ 1 := by
    intro h
    have hall : ∀ a : I.E, a ∈ (algebraMap I.F I.E).range := fun a =>
      (I.cm.fixed a).1 (by have := DFunLike.congr_fun h a; exact this)
    have hsurj : Function.Surjective (Algebra.linearMap I.F I.E) := fun a => by
      obtain ⟨b, hb⟩ := hall a
      exact ⟨b, hb⟩
    have hfr := (LinearEquiv.ofBijective (Algebra.linearMap I.F I.E)
      ⟨(algebraMap I.F I.E).injective, hsurj⟩).finrank_eq
    rw [Module.finrank_self, I.cm.deg2] at hfr
    exact absurd hfr (by norm_num)
  have hcard : Fintype.card Gal(I.E/I.F) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, I.cm.deg2]
  have huniv : (Finset.univ : Finset Gal(I.E/I.F)) = {1, τ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), hcard]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hτ)]
  rfl

theorem trace_form : ∀ (I : AutInst) (v : InfinitePlace I.F) (θ : Ainf I.F ⊗[I.F] I.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ x y : Fin I.n → Ainf I.F ⊗[I.F] I.E, θ (Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) (hR (Ainf I.F) I.cm.sig I.J x y) ⊗ₜ[I.F] (1 : I.E)) = ((∑ i, (if I.ε v i then 2 else -2) * ((((I.P v)⁻¹ *ᵥ fun j => θ (x j)) i).re * (((I.P v)⁻¹ *ᵥ fun j => θ (y j)) i).re + (((I.P v)⁻¹ *ᵥ fun j => θ (x j)) i).im * (((I.P v)⁻¹ *ᵥ fun j => θ (y j)) i).im) : ℝ) : ℂ) := by
  intro I v θ hθ x y
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  have hmul : ∀ (r : Ainf I.F) (e : I.E),
      θ (r ⊗ₜ[I.F] e) = θ (r ⊗ₜ[I.F] (1 : I.E)) * I.φ v e := by
    intro r e
    rw [← hθ.1 e, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hconj : ∀ e : I.E, I.φ v (I.cm.sig e) = (starRingEnd ℂ) (I.φ v e) := by
    intro e
    rw [starRingEnd_apply]
    exact hcm.2.2.2 _ _

  have hB : ∀ z, θ (sigR (Ainf I.F) I.cm.sig z) = (starRingEnd ℂ) (θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e =>
      have hs : sigR (Ainf I.F) I.cm.sig (r ⊗ₜ[I.F] e) = r ⊗ₜ[I.F] I.cm.sig e := by
        simp [sigR, Algebra.TensorProduct.map_tmul]
      rw [hs, hmul r (I.cm.sig e), hmul r e, map_mul, tmul_one_conj_real I v θ hθ r, hconj]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

  have htr1 : ∀ e : I.E, Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) ((1 : Ainf I.F) ⊗ₜ[I.F] e) =
      algebraMap I.F (Ainf I.F) (Algebra.trace I.F I.E e) := by
    intro e
    have hl : Algebra.lmul (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) ((1 : Ainf I.F) ⊗ₜ[I.F] e) =
        (Algebra.lmul I.F I.E e).baseChange (Ainf I.F) := by
      apply LinearMap.ext
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    rw [Algebra.trace_apply, hl, LinearMap.trace_baseChange, Algebra.trace_apply]
  have hA : ∀ z : Ainf I.F ⊗[I.F] I.E,
      θ (Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) z ⊗ₜ[I.F] (1 : I.E)) =
        θ z + (starRingEnd ℂ) (θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e =>
      have hal : θ ((algebraMap I.F (Ainf I.F) (Algebra.trace I.F I.E e)) ⊗ₜ[I.F] (1 : I.E)) =
          I.φ v e + (starRingEnd ℂ) (I.φ v e) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
          hθ.1, algebraMap_trace_eq_add_sig, map_add, hconj]
      have hre : r ⊗ₜ[I.F] e = r • ((1 : Ainf I.F) ⊗ₜ[I.F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have htr : Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) (r ⊗ₜ[I.F] e) =
          r * algebraMap I.F (Ainf I.F) (Algebra.trace I.F I.E e) := by
        rw [hre, map_smul, htr1, smul_eq_mul]
      have hsplit : (r * algebraMap I.F (Ainf I.F) (Algebra.trace I.F I.E e)) ⊗ₜ[I.F] (1 : I.E) =
          (r ⊗ₜ[I.F] (1 : I.E)) *
            (algebraMap I.F (Ainf I.F) (Algebra.trace I.F I.E e) ⊗ₜ[I.F] (1 : I.E)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [htr, hsplit, map_mul, hal, hmul r e, map_mul, tmul_one_conj_real I v θ hθ r]
      ring
    | add a b ha hb => rw [map_add, TensorProduct.add_tmul, map_add, ha, hb, map_add, map_add]; ring
  rw [hA]

  have hC : θ (hR (Ainf I.F) I.cm.sig I.J x y) =
      ∑ i, ∑ j, (starRingEnd ℂ) (θ (x i)) * (I.J.map (I.φ v)) i j * θ (y j) := by
    rw [hR]
    unfold Formalism.UG.hform
    simp only [map_sum, map_mul, hB, JR, Matrix.map_apply, inclR, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, hθ.1]
  have hPu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

  have hD : ∀ a b : Fin I.n → ℂ,
      ∑ i, ∑ j, (starRingEnd ℂ) (a i) * (I.J.map (I.φ v)) i j * b j =
        ∑ i, star (((I.P v)⁻¹ *ᵥ a) i) * ((if I.ε v i then 1 else -1) * ((I.P v)⁻¹ *ᵥ b) i) := by
    intro a b
    have ha : a = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ a) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have hb : b = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ b) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have h1 : ∑ i, ∑ j, (starRingEnd ℂ) (a i) * (I.J.map (I.φ v)) i j * b j =
        star a ⬝ᵥ (I.J.map (I.φ v) *ᵥ b) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]
    rw [h1]
    generalize (I.P v)⁻¹ *ᵥ a = u at ha ⊢
    generalize (I.P v)⁻¹ *ᵥ b = w at hb ⊢
    subst ha hb
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      I.P_spec v]
    simp only [Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  rw [hC, hD, Complex.add_conj]
  congr 1
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] <;> ring

end GlobalTheory.GaussMean.RealDensity
