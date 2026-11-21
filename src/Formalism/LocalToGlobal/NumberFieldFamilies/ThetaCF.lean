import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.BaseFormAnisotropicOrthogonalSingle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gaps

variable (D : D7)

def AtTauU : Prop := ∀ (V : HSp D) (τ : D.what₂.Tau), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau (th0 D) V τ g h

def SmAdd : Prop := ∀ (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFunSm (th0 D) V φ → IsAutFunSm (th0 D) V φ' →
  IsAutFunSm (th0 D) V (φ + φ')

def SmRight : Prop := ∀ (V : HSp D) (k : GA D V), k ∈ GfC V ∨ k ∈ GinfC V → ∀ φ : GA D V → ℂ, IsAutFunSm (th0 D) V φ →
  IsAutFunSm (th0 D) V (rTr V k φ)

def SmConj : Prop := ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm (th0 D) V φ → IsAutFunSm (th0 D) V (star φ)

def CuspInt : Prop := ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ →
  ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (μ : Measure (NI V C)) (𝓕 : Set (NI V C)), μ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓕 μ →
      ∀ g, IntegrableOn (fun n : NI V C => φ ((n : GA D V) * g)) 𝓕 μ

def VolU : Prop := ∀ V : HSp D, V.SigOK → ∀ μ μ' : Measure (GA D V),
  IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ →
  IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ' → μ = μ'

def VolEx : Prop := ∀ V : HSp D, V.SigOK → ∃ μ 𝓕, IsVolPair D V μ 𝓕

def PetInt : Prop := ∀ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure →
  IsFundamentalDomain (GQ V) 𝓕 μ → ∀ φ φ' : GA D V → ℂ, IsAutFunSm (th0 D) V φ → IsAutFunSm (th0 D) V φ' → IsCuspFun V φ' →
    IntegrableOn (fun h => star (φ h) * φ' h) 𝓕 μ

end Gaps

variable {D : D7}

theorem Rder_smul (θ : InfF D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

theorem sm_smul (θ : InfF D) (V : HSp D) (c : ℂ) (φ : GA D V → ℂ) (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) where
  left := fun γ hγ g => by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k a b g => by simp only [Pi.smul_apply, hk k a b g]⟩
  cont := h.cont.const_smul c
  smooth := fun k τs Xs hX g => (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, a, b, e⟩ := h.zfin
    exact ⟨W, a, W.smul_mem c b, e⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    have e : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ),
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
      intro l
      induction l with
      | nil => rfl
      | cons p l ih => rw [List.foldr_cons, List.foldr_cons, ih, Rder_smul]
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [e, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

variable (D) in

def afC (V : HSp D) : Submodule ℂ (GA D V → ℂ) := Submodule.span ℂ {φ | IsAutFunSm (th0 D) V φ}

theorem mem_afC (h : SmAdd D) {V : HSp D} {φ : GA D V → ℂ} : φ ∈ afC D V ↔ IsAutFunSm (th0 D) V φ := by
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isAutFunSm_const _ V 0
  | add x y _ _ hx hy => exact h V x y hx hy
  | smul c x _ hx => exact sm_smul _ V c x hx

def rTrL (V : HSp D) (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * k)

theorem rTrL_mem (h : SmRight D) {V : HSp D} {k : GA D V} (hk : k ∈ GfC V ∨ k ∈ GinfC V) :
    ∀ φ ∈ afC D V, rTrL V k φ ∈ afC D V := by
  intro φ hφ
  unfold afC at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h V k hk x hx)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

def actC (h : SmRight D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V ∨ k ∈ GinfC V) : Module.End ℂ (afC D V) :=
  (rTrL V k).restrict (rTrL_mem h hk)

theorem actC_apply (h : SmRight D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V ∨ k ∈ GinfC V) (F : afC D V) (x : GA D V) :
    (actC h V k hk F).1 x = F.1 (x * k) := rfl

variable (D) in

def cuspC (V : HSp D) : Submodule ℂ (afC D V) := Submodule.span ℂ {F | IsCuspFun V F.1}

theorem mem_cuspC (hA : SmAdd D) (hI : CuspInt D) {V : HSp D} {F : afC D V} : F ∈ cuspC D V ↔ IsCuspFun V F.1 := by
  refine ⟨fun hF => ?_, fun hF => Submodule.subset_span hF⟩
  induction hF using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro r C _ μ 𝓕 _ _ g; simp
  | add x y _ _ hx hy =>
    intro r C hC μ 𝓕 h1 h2 g
    have a := hI V x.1 ((mem_afC hA).1 x.2).toIsAutFun r C hC μ 𝓕 h1 h2 g
    have b := hI V y.1 ((mem_afC hA).1 y.2).toIsAutFun r C hC μ 𝓕 h1 h2 g
    have e := integral_add a b
    rw [hx r C hC μ 𝓕 h1 h2 g, hy r C hC μ 𝓕 h1 h2 g, add_zero] at e
    exact e
  | smul c x _ hx =>
    intro r C hC μ 𝓕 h1 h2 g
    have e := hx r C hC μ 𝓕 h1 h2 g
    show ∫ n in 𝓕, c * x.1 ((n : GA D V) * g) ∂μ = 0
    rw [integral_const_mul, e, mul_zero]

theorem emb_star (τ : D.host.E →+* ℂ) (x : D.host.E) : τ (star x) = starRingEnd ℂ (τ x) := by
  exact @NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ _ D.host.isCMField_hostE _ τ x

theorem gram_herm (V : HSp D) (τ : D.host.E →+* ℂ) : Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map τ) := by
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
  rw [← emb_star]
  congr 1
  have := V.herm.eq (V.frame j) (V.frame i)
  rw [starRingEnd_apply] at this
  exact this

theorem sig_ex (V : HSp D) (τ : D.host.E →+* ℂ) : ∃ s : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map τ) s.1 s.2 := by
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ (V.gram.map τ) (gram_herm V τ) (by
    have : (V.gram.map τ).det = τ V.gram.det := (τ.map_det V.gram).symm
    rw [this]
    exact ((map_ne_zero τ).2 (gram_det_ne V)).isUnit)
  exact ⟨(p, q), h⟩

open Classical in

def fixSig (V : HSp D) : HSp D := { V with sig := if V.SigOK then V.sig else fun τ => (sig_ex V τ).choose }

theorem fixSig_ok (V : HSp D) : (fixSig V).SigOK := by
  unfold HSpace.SigOK
  intro τ
  by_cases h : V.SigOK
  · simp only [fixSig, h, if_true]
    exact h τ
  · simp only [fixSig, h, if_false]
    exact (sig_ex V τ).choose_spec

def GoodPair (V : HSp D) (p : Measure (GA D V) × Set (GA D V)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) p.2 p.1 ∧ (V.SigOK → IsVolPair D V p.1 p.2)

theorem goodPair_iff (V : HSp D) (p : Measure (GA D V) × Set (GA D V)) :
    GoodPair V p ↔ GoodPairR D.sp.cm (tauE D) D.cd V p :=
  ⟨fun h => ⟨h.1, h.2.1, fun a => (h.2.2 a).1⟩, fun h => ⟨h.1, h.2.1, fun a => ⟨h.2.2 a, h.2.1⟩⟩⟩

theorem goodPair_ex (h : VolEx D) (V : HSp D) : ∃ p, GoodPair V p := by
  by_cases hV : V.SigOK
  · obtain ⟨μ, 𝓕, e⟩ := h V hV
    exact ⟨(μ, 𝓕), e.1.1, e.2, fun _ => e⟩
  · obtain ⟨μ, 𝓕, e⟩ := h (fixSig V) (fixSig_ok V)
    exact ⟨(μ, 𝓕), e.1.1, e.2, fun a => absurd a hV⟩

def pairC (V : HSp D) : Measure (GA D V) × Set (GA D V) := pairR D.sp.cm (tauE D) D.cd V

theorem pairC_spec (h : VolEx D) (V : HSp D) : GoodPair V (pairC V) := by
  have e : ∃ p, GoodPairR D.sp.cm (tauE D) D.cd V p := (goodPair_ex h V).imp fun p hp => (goodPair_iff V p).1 hp
  rw [goodPair_iff]
  unfold pairC pairR
  rw [dif_pos e]
  exact e.choose_spec

def intC (V : HSp D) (f : GA D V → ℂ) : ℂ := ∫ h in (pairC V).2, f h ∂(pairC V).1

theorem petR_ex (p q : ℕ) : ∃ c : ℝ, 0 < c ∧ OmegaDensity (ENNReal.ofReal c • D.cd.cd p q) (minfDensity (p + q)) := by
  obtain ⟨c, h0, ht, ⟨lam, hl, hlim⟩, -⟩ := D.cd.trick p q
  have m0 : minfDensity (p + q) ≠ 0 := by unfold minfDensity; simp
  have mt : minfDensity (p + q) ≠ ⊤ := by unfold minfDensity; simp
  have d0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨m0, ht⟩
  have dt : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top mt h0
  refine ⟨(minfDensity (p + q) / c).toReal, ENNReal.toReal_pos d0 dt, lam, hl, ?_⟩
  rw [ENNReal.ofReal_toReal dt]
  have := ENNReal.Tendsto.const_mul (a := minfDensity (p + q) / c) hlim (Or.inr dt)
  rw [ENNReal.div_mul_cancel h0 ht] at this
  refine this.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

variable (D) in

def petRC (p q : ℕ) : ℝ := if p = 0 ∨ q = 0 then 1 else (petR_ex (D := D) p q).choose

end Formalism.L2.Fam.ThC

end
