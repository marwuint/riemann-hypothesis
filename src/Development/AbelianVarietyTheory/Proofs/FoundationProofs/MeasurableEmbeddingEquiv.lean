import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set GlobalTheory.AdelicU GlobalTheory.OpTrace NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.Orb

section Operators

variable {H H' V W : Type} [Group H] [Group H'] [MeasurableSpace H] [MeasurableSpace H']
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem repOp_congr {π : H →* (V →L[ℂ] V)} {π' : H' →* (V →L[ℂ] V)} {μ : Measure H} {μ' : Measure H'} {f : H → ℂ}
    {f' : H' → ℂ} (h : ∀ T, IsRepOp π μ f T ↔ IsRepOp π' μ' f' T) : repOp π μ f = repOp π' μ' f' := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    rw [hT.repOp_eq, ((h T).1 hT).repOp_eq]
  · rw [repOp, repOp, dif_neg hT, dif_neg fun ⟨T, h'⟩ => hT ⟨T, (h T).2 h'⟩]

theorem IsUnitEquiv.symm {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') :
    IsUnitEquiv π' π := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.symm, fun g v => A.injective (by simp [hA])⟩

theorem IsUnitEquiv.trans {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : H →* (V →L[ℂ] V)}
    {π' : H →* (W →L[ℂ] W)} {π'' : H →* (U →L[ℂ] U)} (h : IsUnitEquiv π π') (h' : IsUnitEquiv π' π'') :
    IsUnitEquiv π π'' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨B, hB⟩ := h'
  exact ⟨A.trans B, fun g v => by simp [hA, hB]⟩

variable [CompleteSpace V] [CompleteSpace W]

theorem isRepOp_conj {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (A : V ≃ₗᵢ[ℂ] W)
    (hA : ∀ g v, A (π g v) = π' g (A v)) {μ : Measure H} {f : H → ℂ} {T : V →L[ℂ] V} (h : IsRepOp π μ f T) :
    IsRepOp π' μ f ((A.toContinuousLinearEquiv : V →L[ℂ] W) ∘L T ∘L
      (A.toContinuousLinearEquiv.symm : W →L[ℂ] V)) := fun w => by
  obtain ⟨h1, h2⟩ := h (A.symm w)
  have e : ∀ g, f g • π' g w = (A.toContinuousLinearEquiv : V →L[ℂ] W) (f g • π g (A.symm w)) := fun g => by
    simp [hA]
  simp only [e]
  refine ⟨ContinuousLinearMap.integrable_comp _ h1, ?_⟩
  rw [ContinuousLinearMap.integral_comp_comm _ h1, ← h2]
  rfl

theorem IsUnitEquiv.hasTrace {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') {μ : Measure H}
    {f : H → ℂ} {c : ℂ} (ht : HasTrace (repOp π μ f) c) : HasTrace (repOp π' μ f) c := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    obtain ⟨A, hA⟩ := h
    rw [hT.repOp_eq] at ht
    rw [(isRepOp_conj A hA hT).repOp_eq]
    exact ⟨ht.1.comp_comp _ _, (ht.1.trace_conj _).trans ht.2⟩
  · obtain ⟨A, hA⟩ := h.symm
    rw [repOp, dif_neg hT] at ht
    rw [repOp, dif_neg fun ⟨T, h'⟩ => hT ⟨_, isRepOp_conj A hA h'⟩]
    exact ⟨isTraceClass_zero, trace_zero.trans (trace_zero.symm.trans ht.2)⟩

end Operators

section Transport

variable {H H' n V W : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H'] [Fintype n]
  [DecidableEq n] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (e : H ≃ₜ* H') {ι : H →* Matrix n n ℂ} {ι' : H' →* Matrix n n ℂ} {a : Matrix n n ℂ}

variable {e}

theorem comp_mem_ccMat (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {f' : H' → ℂ} (h : f' ∈ CcMat ι') :
    f' ∘ e ∈ CcMat ι := by
  obtain ⟨hc, Φ, hΦ, hf⟩ := h
  refine ⟨hc.comp_homeomorph e.toHomeomorph, Φ ∘ fun y i j => ∑ l, (∑ k, a i k * y k l) * a⁻¹ l j,
    hΦ.comp (by fun_prop), fun g => (hf _).trans (congrArg Φ ?_)⟩
  funext i j
  simp only [matCoord, hι, Matrix.mul_apply]

theorem isRegSS_conj_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (s : H) :
    IsRegSS (ι' (e s)) ↔ IsRegSS (ι s) := by
  rw [IsRegSS, IsRegSS, hι, Matrix.charpoly_mul_comm,
    Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 ha)]

variable (e) in

theorem isCompact_cent_iff (s : H) : IsCompact (cent (e s) : Set H') ↔ IsCompact (cent s : Set H) := by
  rw [isCompact_iff_compactSpace, isCompact_iff_compactSpace]
  exact ⟨fun _ => (centEquiv e s rfl).toHomeomorph.symm.compactSpace,
    fun _ => (centEquiv e s rfl).toHomeomorph.compactSpace⟩

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H'] (e)

theorem measurableEmbedding_equiv : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding

theorem repOp_map (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) (f' : H' → ℂ) :
    repOp π' (μ.map e) f' = repOp (π'.comp (e : H →* H')) μ (f' ∘ e) :=
  repOp_congr fun T => forall_congr' fun v => and_congr (measurableEmbedding_equiv e).integrable_map_iff
    (by rw [(measurableEmbedding_equiv e).integral_map]; rfl)

variable {e} [CompleteSpace V]

variable [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [IsTopologicalGroup H'] [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H']

end Transport

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem exists_frameMat_eq (ρ : D.what₂.Tau) {x : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hx : x ∈ UJset (M.ε ρ)) :
    ∃ g, frameMat M ρ g = x := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have e : M.fr ρ * ((M.fr ρ)⁻¹ * x * M.fr ρ) * (M.fr ρ)⁻¹ = x := by
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
  obtain ⟨g, hg⟩ := exists_archEquiv_eq V (embOverOf D ρ) rfl ((conj_mem_UJset_iff M ρ _).1 (e.symm ▸ hx))
  exact ⟨g, (congrArg (M.fr ρ * · * (M.fr ρ)⁻¹) hg).trans e⟩

theorem isEmbedding_frameMat (ρ : D.what₂.Tau) : Topology.IsEmbedding (frameMat M ρ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have h : Topology.IsEmbedding fun x : Matrix (Fin V.rank) (Fin V.rank) ℂ => M.fr ρ * x * (M.fr ρ)⁻¹ :=
    Function.LeftInverse.isEmbedding (f := fun x => (M.fr ρ)⁻¹ * x * M.fr ρ) (fun x => by
      simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  exact h.comp (isEmbedding_archMat V.gram (isCMExt_host D) (embOverOf D ρ))

def frameHom (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* Formalism.REAL.UJ (M.ε ρ) :=
  (frameMat M ρ).toHomUnits.codRestrict _ (frameMat_mem M ρ)

theorem frameHom_bijective (ρ : D.what₂.Tau) : Function.Bijective (frameHom M ρ) :=
  ⟨fun _ _ h => (isEmbedding_frameMat M ρ).injective (congrArg (ujMat (M.ε ρ)) h), fun x => by
    obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ (x := ujMat (M.ε ρ) x) x.2
    exact ⟨g, Subtype.ext (Units.ext hg)⟩⟩

theorem isEmbedding_ujMat {m : ℕ} (ε : Fin m → Bool) : Topology.IsEmbedding (ujMat ε) :=
  (Formalism.REAL.isClosedEmbeddingMatrix m ε).1.isEmbedding

def frameEquiv (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) ≃ₜ* Formalism.REAL.UJ (M.ε ρ) :=
  { MulEquiv.ofBijective _ (frameHom_bijective M ρ) with
    continuous_toFun := (isEmbedding_ujMat _).continuous_iff.2 (isEmbedding_frameMat M ρ).continuous
    continuous_invFun := (isEmbedding_frameMat M ρ).continuous_iff.2 ((isEmbedding_ujMat _).continuous.congr
      fun x => congrArg (ujMat (M.ε ρ))
        ((MulEquiv.ofBijective _ (frameHom_bijective M ρ)).apply_symm_apply x).symm) }

theorem ujMat_frameEquiv_eq_conj (ρ : D.what₂.Tau) (g : GArch D.sp.cm.sig V.gram (placeOf D ρ)) :
    ujMat (M.ε ρ) (frameEquiv M ρ g) = M.fr ρ * matAt V ρ g * (M.fr ρ)⁻¹ := rfl

end Record

end GlobalTheory.Orb
