import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegersMemInverseHalfDifferent

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.Glob

section Image

variable {LL : Type} [Field LL] [NumberField LL] (ι : LL →+* ℂ)

abbrev imM : IntermediateField ℚ ℂ := ι.toRatAlgHom.fieldRange

def imEquiv : LL ≃ₐ[ℚ] imM ι := AlgEquiv.ofInjectiveField ι.toRatAlgHom

@[simp] theorem coe_imEquiv (x : LL) : ((imEquiv ι x : imM ι) : ℂ) = ι x := rfl

instance imM_numberField : NumberField (imM ι) where
  to_finiteDimensional := LinearEquiv.finiteDimensional (imEquiv ι).toLinearEquiv

def rhoOf (s : LL →+* ℂ) : imM ι →ₐ[ℚ] ℂ := s.toRatAlgHom.comp (imEquiv ι).symm.toAlgHom

@[simp] theorem rhoOf_imEquiv (s : LL →+* ℂ) (x : LL) : rhoOf ι s (imEquiv ι x) = s x := by
  simp [rhoOf]

def rhoEquiv : (LL →+* ℂ) ≃ (imM ι →ₐ[ℚ] ℂ) where
  toFun := rhoOf ι
  invFun ρ := (ρ.comp (imEquiv ι).toAlgHom).toRingHom
  left_inv s := by ext x; simp
  right_inv ρ := by
    ext x
    obtain ⟨y, rfl⟩ := (imEquiv ι).surjective x
    simp

@[simp] theorem rhoEquiv_apply (s : LL →+* ℂ) : rhoEquiv ι s = rhoOf ι s := rfl

end Image

section Curve

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}

theorem lamConj_cases (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (cc' : Ideal (𝓞 D.host.K)) (δ' : ℂ), Crv D cc' δ' ∧
      (lamConj M ρ (lamOf D cc δ) = lamOf D cc' δ' ∨
        (lamConj M ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc' δ') := by
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ h M ρ hM
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc δ h M ρ hfix hM.2.1 hM.2.2 1 one_pos
    exact ⟨cc', δ', hc', Or.inl e⟩
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc δ h M (rhoBar M ρ) hfix hM.2.1 hM.2.2 1 one_pos
    refine ⟨cc', δ', hc', Or.inr ?_⟩
    rw [← e]
    exact (congrArg Tor.abelian₂ hbar).symm

theorem isLat_lamConj (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    GlobalTheory.ThetaConj.IsLat (lamConj M ρ (lamOf D cc δ)) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e]; exact GlobalTheory.ThetaConj.isLat_lamOf h'
  · rw [← GlobalTheory.ThetaConj.conj_conj_lat (lamConj M ρ (lamOf D cc δ)), e]
    exact (GlobalTheory.ThetaConj.isLat_lamOf h').conj

theorem area_lamConj_pos (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    0 < area (lamConj M ρ (lamOf D cc δ)) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e]; exact GlobalTheory.ConjJet.area_pos D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h'
  · rw [← GlobalTheory.ThetaConj.area_conj, e]
    exact GlobalTheory.ConjJet.area_pos D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h'

theorem isThetaZero_unique_lattice (h : Crv D cc δ) {t t' : ℂ} (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t') : t - t' ∈ lamOf D cc δ := by
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine GlobalTheory.ThetaConj.two_torsion_unique (GlobalTheory.ThetaConj.isLat_lamOf h) (w0 D) k hk ht.1 ht.2.1 ht.2.2
    ht'.1 ht'.2.1 ht'.2.2 ?_
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem isThetaZero_unique (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t') :
    t - t' ∈ lamConj M ρ (lamOf D cc δ) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ht' ⊢; exact isThetaZero_unique_lattice h' ht ht'
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    have h2 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht'
    rw [e] at h1 h2
    have := isThetaZero_unique_lattice h' h1 h2
    rw [← e, GlobalTheory.ThetaConj.mem_conj] at this
    simpa using this

theorem exists_isThetaZero (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t :=
  (GlobalTheory.TwoTorsionPt.exists_point D cc δ h).2 M ρ hM.2.1 hM.2.2

theorem thetaZero_eq_of_isThetaZero (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t') :
    GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t = GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t' := by
  have := GlobalTheory.ThetaConj.evenTheta_add_lattice_mem (isLat_lamConj h hM ρ) t' (isThetaZero_unique h hM ρ ht ht')
  rwa [add_sub_cancel] at this

theorem normSq1_eq_nrm1Sq (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.normSq1 Λ G = nrm1Sq Λ G := by
  unfold GL3Theta.normSq1 nrm1Sq
  have : ∀ z : ℂ, -Real.pi * (GL3Theta.hf1 Λ z z).re = -Real.pi * ‖z‖ ^ 2 / area Λ := fun z => by
    unfold GL3Theta.hf1
    rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    ring
  simp only [this]

theorem normSq1_nonneg (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : 0 ≤ GL3Theta.normSq1 Λ G := by
  unfold GL3Theta.normSq1
  simp only [MeasureTheory.average]
  exact MeasureTheory.integral_nonneg fun z => by positivity

theorem normSq_thetaZero_pos (h : Crv D cc δ) (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    0 < GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) := by
  refine lt_of_le_of_ne (normSq1_nonneg _ _) (Ne.symm ?_)
  rw [normSq1_eq_nrm1Sq]
  have hl := isLat_lamConj h hM ρ
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ⊢
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc' δ' t h' ht
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    rw [← GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq _ hl t]
    rw [e] at h1 ⊢
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc' δ' _ h' h1

end Curve

section Line

variable {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]

theorem ellT_ne_bot (hM : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) : ellT D M τ ≠ ⊥ := by
  first
  | exact @_root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot
  | exact _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot
  | (apply _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot <;> assumption)
  | (intros; apply _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InverseHalfDifferent.ellT_ne_bot ..)

theorem ne_zero_of_span_eq (hM : ∀ τ x, embT D τ x ∈ M) {τ : D.what₂.Tau} {a : M}
    (ha : Submodule.span (𝓞 M) {a} = ellT D M τ) : a ≠ 0 := by
  rintro rfl
  exact ellT_ne_bot hM τ (by rw [← ha, Submodule.span_singleton_eq_bot])

omit [NumberField M] in

theorem logMet_mul {Λ : AddSubgroup ℂ} {ρ : M →ₐ[ℚ] ℂ} (hΛ : 0 < area (lamConj M ρ Λ)) {c a : M}
    (hc : c ≠ 0) (ha : a ≠ 0) :
    logMet M Λ ρ (c * a) = 2 * Real.log ‖ρ c‖ + logMet M Λ ρ a := by
  have h1 : 0 < ‖ρ a‖ := norm_pos_iff.2 ((map_ne_zero ρ).2 ha)
  have h2 : 0 < ‖ρ c‖ := norm_pos_iff.2 ((map_ne_zero ρ).2 hc)
  have := Real.pi_pos
  unfold logMet
  rw [map_mul, norm_mul, show Real.pi * (‖ρ c‖ * ‖ρ a‖) ^ 2 / area (lamConj M ρ Λ) =
    ‖ρ c‖ ^ 2 * (Real.pi * ‖ρ a‖ ^ 2 / area (lamConj M ρ Λ)) by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  norm_num

theorem index_span_mul (c : 𝓞 M) {a : M} (ha : a ≠ 0) :
    ((Submodule.span (𝓞 M) {c • a}).toAddSubgroup.addSubgroupOf
      (Submodule.span (𝓞 M) {a}).toAddSubgroup).index = Ideal.absNorm (Ideal.span {c}) := by
  let f : 𝓞 M →ₗ[𝓞 M] M := LinearMap.toSpanSingleton (𝓞 M) M a
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact LinearMap.ker_toSpanSingleton (𝓞 M) ha
  have h1 : (Submodule.span (𝓞 M) {a}).toAddSubgroup = (⊤ : AddSubgroup (𝓞 M)).map f.toAddMonoidHom := by
    ext x
    simp [f, Submodule.mem_span_singleton]
  have h2 : (Submodule.span (𝓞 M) {c • a}).toAddSubgroup =
      (Ideal.span {c} : Ideal (𝓞 M)).toAddSubgroup.map f.toAddMonoidHom := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, AddSubgroup.mem_map,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r * c, ⟨r, rfl⟩, by simp [f, mul_smul]⟩
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp [f, mul_smul]⟩
  change AddSubgroup.relIndex _ _ = _
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  rfl

theorem sum_log_norm (c : 𝓞 M) (hc : c ≠ 0) :
    ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ (c : M)‖ = Real.log (Ideal.absNorm (Ideal.span {c}) : ℕ) := by
  have hc' : (c : M) ≠ 0 := by simpa using hc
  rw [← Real.log_prod (fun ρ _ => norm_ne_zero_iff.2 ((map_ne_zero ρ).2 hc')), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ (c : M), Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem meanLogOm_eq_of_gen (hM : ∀ τ x, embT D τ x ∈ M) {Λ : AddSubgroup ℂ}
    (hΛ : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ Λ)) {τ : D.what₂.Tau} {a : M}
    (ha : Submodule.span (𝓞 M) {a} = ellT D M τ) :
    meanLogOm D Λ M τ = -(∑ ρ : M →ₐ[ℚ] ℂ, logMet M Λ ρ a) / (Module.finrank ℚ M : ℝ) := by
  have ha0 := ne_zero_of_span_eq hM ha
  have hs := Classical.epsilon_spec (p := fun s : M => s ≠ 0 ∧ s ∈ ellT D M τ)
    ⟨a, ha0, ha ▸ Submodule.mem_span_singleton_self a⟩
  unfold meanLogOm
  simp only
  generalize Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ ellT D M τ) = s at hs ⊢
  obtain ⟨hs0, hs⟩ := hs
  rw [← ha] at hs ⊢
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
  have hc : c ≠ 0 := by rintro rfl; simp at hs0
  have hc' : (c : M) ≠ 0 := by simpa using hc
  rw [index_span_mul c ha0, ← sum_log_norm c hc]
  have : ∀ ρ : M →ₐ[ℚ] ℂ, logMet M Λ ρ (c • a) = 2 * Real.log ‖ρ (c : M)‖ + logMet M Λ ρ a :=
    fun ρ => logMet_mul (hΛ ρ) hc' ha0
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Line

section Comparison₂

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

structure ExtraTie {LL : Type} [Field LL] [NumberField LL] (ι : LL →+* ℂ)
    (G : GlobalExtra LL D.what₂.Tau) (a : D.what₂.Tau → imM ι) : Prop where

  crv : Crv D cc δ

  data : DataIn D (tor0 D cc δ) (imM ι)

  gen : ∀ τ, Submodule.span (𝓞 (imM ι)) {a τ} = ellT D (imM ι) τ

  om : ∀ τ (s : LL →+* ℂ),
    G.Om τ s = Real.exp (-logMet (imM ι) (lamOf D cc δ) (rhoOf ι s) (a τ))

  th : ∀ (s : LL →+* ℂ) (t : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ)) t →
    G.thOne s ^ 2 = GL3Theta.normSq1 (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ))
      (GL3Theta.th0 (lamConj (imM ι) (rhoOf ι s) (lamOf D cc δ)) t)

abbrev coefM : IntermediateField ℚ ℂ := imM D.what₂.embLL

def PerTie : Prop :=
  Crv D cc δ ∧ DataIn D (tor0 D cc δ) (coefM D) ∧
  (∀ τ : D.what₂.Tau, ∃ a : coefM D, Submodule.span (𝓞 (coefM D)) {a} = ellT D (coefM D) τ ∧
    ∀ s : D.what₂.LL →+* ℂ, D.gx.Om τ s =
      Real.exp (-logMet (coefM D) (lamOf D cc δ) (rhoOf D.what₂.embLL s) a)) ∧
  ∀ (s : D.what₂.LL →+* ℂ) (t : ℂ),
    GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (coefM D) (rhoOf D.what₂.embLL s) (lamOf D cc δ)) t →
    D.gx.thOne s ^ 2 = GL3Theta.normSq1 (lamConj (coefM D) (rhoOf D.what₂.embLL s) (lamOf D cc δ))
      (GL3Theta.th0 (lamConj (coefM D) (rhoOf D.what₂.embLL s) (lamOf D cc δ)) t)

variable {D cc δ}

variable {LL : Type} [Field LL] [NumberField LL] {ι : LL →+* ℂ}

namespace ExtraTie

end ExtraTie

namespace PerTie

end PerTie

end Comparison₂

section Free

variable {D : D7}

theorem sum_dual_family {r : ℕ} {a a' : Fin r → D.host.E}
    (h : ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k)
    (τ σ : D.what₂.Tau) :
    ∑ k, embT D τ (D.host.conj (a' k)) * embT D σ (a k) = if τ = σ then 1 else 0 := by
  rw [← sub_eq_zero]
  refine GlobalTheory.OrthoCoord.embT_indep
    (fun τ => ∑ k, embT D τ (D.host.conj (a' k)) * embT D σ (a k) - if τ = σ then 1 else 0) (fun t => ?_) τ
  have h1 := congrArg (embT D σ) (h t)
  rw [map_sum] at h1
  have h2 : ∀ k, embT D σ ((Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) =
      ∑ τ, embT D τ (D.host.conj (a' k)) * embT D σ (a k) * embT D τ t := fun k => by
    rw [Algebra.smul_def, map_mul]
    have e1 := GlobalTheory.InducedType.restrict_K D σ (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k)))
    have e2 := GlobalTheory.InducedType.sum_eq_trace D (t * D.host.conj (a' k))
    erw [e1, ← e2]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul]; ring
  simp only [h2] at h1
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm, ← h1, sub_self]

theorem mem_ellT_iff {M : IntermediateField ℚ ℂ} [NumberField M] (hM : ∀ τ x, embT D τ x ∈ M)
    (τ : D.what₂.Tau) (x : M) :
    x ∈ ellT D M τ ↔ ∀ y ∈ D.host.AA0, IsIntegral ℤ ((x : ℂ) * embT D τ (D.host.conj y)) := by
  unfold ellT
  rw [Submodule.mem_comap]
  constructor
  · intro hx y hy
    have key : ∀ v ∈ mmM D M, IsIntegral ℤ (∑ σ, (v σ : ℂ) * embT D σ (D.host.conj y)) := by
      intro v hv
      unfold mmM at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        simp only [TaylorLogMetric.liftM, dif_pos (hM _ _), ← map_mul]
        have e2 := GlobalTheory.InducedType.sum_eq_trace D (a * D.host.conj y)
        erw [e2]
        obtain ⟨c, hc⟩ := (factMMUnimodular D.R D.host a).1 ha y hy
        have hi : IsIntegral ℤ (Algebra.trace D.host.K D.host.E (a * D.host.conj y)) := by
          rw [← hc]; exact c.isIntegral_coe
        exact map_isIntegral_int (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) hi
      | zero => simpa using isIntegral_zero
      | add x y _ _ hx hy =>
        simpa only [Pi.add_apply, IntermediateField.coe_add, add_mul, Finset.sum_add_distrib] using hx.add hy
      | smul c x _ hx =>
        have hc : IsIntegral ℤ (((c : M) : ℂ)) := map_isIntegral_int (M.val : M →+* ℂ) c.isIntegral_coe
        convert hc.mul hx using 1
        · rfl
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← mul_assoc]
        rfl
    have := key _ hx
    rwa [Finset.sum_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), LinearMap.coe_single,
      Pi.single_eq_same] at this
  · intro hx
    obtain ⟨r, a, a', ha, ha', h⟩ := GlobalTheory.exists_trace_dual_family_halfDifferent D
    let c : Fin r → 𝓞 M := fun k => ⟨x * ⟨_, hM τ (D.host.conj (a' k))⟩,
      (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 (hx _ (ha' k))⟩
    have : ∑ k, c k • (fun σ => TaylorLogMetric.liftM M (embT D σ (a k))) ∈ mmM D M :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a k, ha k, rfl⟩)
    convert this using 1
    funext σ
    apply Subtype.ext
    have e : ∀ k, (((c k • (fun σ => TaylorLogMetric.liftM M (embT D σ (a k)))) σ : M) : ℂ) =
        (x : ℂ) * (embT D τ (D.host.conj (a' k)) * embT D σ (a k)) := fun k => by
      simp only [TaylorLogMetric.liftM, dif_pos (hM _ _), Pi.smul_apply]
      rw [← mul_assoc]
      rfl
    rw [Finset.sum_apply, IntermediateField.coe_sum]
    simp only [e]
    rw [← Finset.mul_sum, sum_dual_family h]
    by_cases hσ : τ = σ
    · subst hσ; simp
    · simp [hσ, Ne.symm hσ]

end Free

end GlobalTheory.Glob
