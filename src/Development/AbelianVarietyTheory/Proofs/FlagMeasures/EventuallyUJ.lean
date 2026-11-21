import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalytic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDerLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IteratedDerivLine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeAnalytic

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGap

open GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

variable {n : ℕ} {ε : Fin n → Bool}

local notation "Mt" => Matrix (Fin n) (Fin n) ℂ

section Local
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAn_conj {f : Mt → ℂ} (h : LocAn ε f) : LocAn ε (fun g => f (g.map star)) := by
  intro g hg
  obtain ⟨F, hF, he⟩ := h _ (UJ_star hg)
  let c : Mt →ₗ[ℝ] Mt :=
    { toFun := fun x => x.map star
      map_add' := fun x y => by ext i j; simp
      map_smul' := fun r x => by ext i j; simp }
  have hc : AnalyticAt ℝ (fun x : Mt => x.map star) g := (LinearMap.toContinuousLinearMap c).analyticAt g
  refine ⟨fun x => F (x.map star), hF.comp_of_eq hc rfl, ?_⟩
  filter_upwards [hc.continuousAt.eventually he] with z hz hzJ
  exact hz (UJ_star hzJ)

theorem locAn_line {f : Mt → ℂ} (h : LocAn ε f) {X : Mt} (hX : inG ε X) :
    AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ := by
  intro t _
  obtain ⟨F, hF, he⟩ := h _ (exp_indefinite_unitary_holds n ε X hX t)
  have h1 := analyticAt_curveR 1 X t
  simp only [Matrix.one_mul] at h1
  refine (hF.comp_of_eq h1 rfl).congr ?_
  filter_upwards [h1.continuousAt.eventually he] with s hs
  exact (hs (exp_indefinite_unitary_holds n ε X hX s)).symm

theorem eab_local {f f' : Mt → ℂ} {g : Mt} (hg : inUJ ε g) (h : ∀ᶠ z in 𝓝 g, inUJ ε z → f z = f' z) (a b : Fin n) :
    Eab ε a b f g = Eab ε a b f' g := by
  have hR : ∀ X, inG ε X → Rd X f g = Rd X f' g := fun X hX => by
    have h1 := (analyticAt_curveR g X 0).continuousAt.tendsto
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [h1.eventually h] with t ht
    exact ht (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))
  have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  simp only [Eab, Ec, hR _ hc.1, hR _ hc.2.1]

end Local

theorem eab_const_mul (c : ℂ) (f : Mt → ℂ) (a b : Fin n) (g : Mt) :
    Eab ε a b (fun z => c * f z) g = c * Eab ε a b f g := by
  simp only [Eab, Ec, Rd, deriv_const_mul_field']
  ring

theorem eventually_UJ {p : Mt → Prop} (h : ∀ᶠ g : UJ ε in 𝓝 1, p (umat g)) :
    ∀ᶠ y in 𝓝 (1 : Mt), inUJ ε y → p y := by
  rw [(isClosedEmbeddingMatrix n ε).1.isEmbedding.isInducing.nhds_eq_comap, eventually_comap] at h
  filter_upwards [h] with y hy hyJ
  obtain ⟨a, rfl⟩ : y ∈ Set.range (fun g : UJ ε => toM g) := by
    rw [(isClosedEmbeddingMatrix n ε).2]; exact hyJ
  exact hy a rfl

theorem exists_gap {lam : Fin n → ℝ} (hlam : IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    ∃ g₀ : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g₀ ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g₀ := by
  by_cases hex : ∃ a b, ε a ≠ ε b
  · refine ⟨h, fun a b hab hne => ?_, ?_⟩
    · have := hgap a b hne
      rwa [abs_of_pos (sub_pos.2 (hlam.1 hab))] at this
    · obtain ⟨a, b, hab⟩ := hex
      have hn : (0 : ℝ) < n := by exact_mod_cast a.pos
      have hq : 1 ≤ rkR ε := by
        unfold rkR
        simp only [le_min_iff, Finset.one_le_card]
        cases ha : ε a <;> cases hb : ε b
        · simp [ha, hb] at hab
        · exact ⟨⟨b, by simp [hb]⟩, ⟨a, by simp [ha]⟩⟩
        · exact ⟨⟨a, by simp [ha]⟩, ⟨b, by simp [hb]⟩⟩
        · simp [ha, hb] at hab
      have : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
      nlinarith
  · exact ⟨2 * n + 1, fun a b _ hne => absurd ⟨a, b, hne⟩ hex, by linarith⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {S : Submodule ℂ H} [S.HasOrthogonalProjection]

theorem proj_comm (hσ : IsURepOn (Kset ε) σ) (hS : IsKStableOn ε σ S) {k : Mt} (hk : k ∈ Kset ε) (x : H) :
    S.starProjection (σ k x) = σ k (S.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.starProjection_apply_mem x)) fun s hs => ?_
  rw [← map_sub, inner_rep_K hσ hk]
  exact Submodule.starProjection_inner_eq_zero x _ (hS _ (Kset_star ε hk) s hs)

theorem ps_entry {lam abelian₂ : Fin n → ℝ} {w : S} {τ : Mt → (S →L[ℂ] S)} (hτ : IsTau ε abelian₂ τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) {z : Mt} (hz : z.map star ∈ U1 ε) (x y : H) :
    ⟪S.orthogonalProjectionOnto y, ps ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ = (Module.finrank ℂ S : ℂ) *
      ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
        (⟪y, σ (toMK k) (w : H)⟫_ℂ * ⟪σ (toMK k) (w : H), x⟫_ℂ) ∂(muK ε) := by
  rw [inner_ps lam hτ _ _ hz, intK, ← integral_const_mul]
  simp only [pk]
  rw [← muConj n ε (fun k => Phi lam (k⁻¹ * z.map star * k) * ((Module.finrank ℂ S : ℂ) *
    (⟪τ k w, S.orthogonalProjectionOnto x⟫_ℂ * ⟪S.orthogonalProjectionOnto y, τ k w⟫_ℂ)))]
  congr 1
  funext k
  have hk : toMK k ∈ Kset ε := k.2
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    hτσ _ (K_star hk), map_star_star, K_inv (K_star hk), map_star_ct, ← map_star_mul, ← map_star_mul, ← K_inv hk]
  ring

def diffOp (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Mt → (H →L[ℂ] H)) (τ : Mt → (S →L[ℂ] S)) (w : S) (z : Mt) :
    H →L[ℂ] H :=
  S.starProjection.comp (σ z) - S.subtypeL.comp ((Psi ε lam τ w (z.map star)).comp S.orthogonalProjectionOnto)

theorem diffOp_apply (lam : Fin n → ℝ) (τ : Mt → (S →L[ℂ] S)) (w : S) (z : Mt) (x : H) :
    diffOp ε lam σ τ w z x =
      S.starProjection (σ z x) - (Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x) : S) := rfl

theorem inner_diffOp (lam : Fin n → ℝ) (τ : Mt → (S →L[ℂ] S)) (w : S) (x y : H) :
    (fun z => ⟪y, diffOp ε lam σ τ w z x⟫_ℂ) = fun z => ⟪S.starProjection y, σ z x⟫_ℂ +
      (-1) * ⟪S.orthogonalProjectionOnto y, Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ := by
  funext z
  rw [diffOp_apply, inner_sub_right, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_starProjection_left_eq_right]
  ring

theorem diffOp_equiv {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hσ : IsURepOn (UJset ε) σ) (hS : IsKStableOn ε σ S)
    {w : S} {τ : Mt → (S →L[ℂ] S)} (hτ : IsTau ε (lowK ε lam) τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) {g k₁ k₂ : Mt} (hg : g ∈ UJset ε)
    (h₁ : k₁ ∈ Kset ε) (h₂ : k₂ ∈ Kset ε) (x : H) :
    diffOp ε lam σ τ w (k₁ * g * k₂) x = σ k₁ (diffOp ε lam σ τ w g (σ k₂ x)) := by
  have e : τ (k₂.map star) (S.orthogonalProjectionOnto x) = S.orthogonalProjectionOnto (σ k₂ x) := by
    apply Subtype.ext
    rw [hτσ _ (K_star h₂), map_star_star]
    exact (proj_comm (URep_K hσ) hS h₂ x).symm
  rw [diffOp_apply, diffOp_apply, map_sub, ← proj_comm (URep_K hσ) hS h₁, map_star_mul, map_star_mul,
    (psiPolar n ε lam S τ w hlam hτ).2.2 _ (K_star h₁) _ (K_star h₂) _ (UJ_star hg),
    hσ.1.2 _ (indefinite_unitary_mul_mem ε (K_UJ h₁) hg) _ (K_UJ h₂), hσ.1.2 _ (K_UJ h₁) _ hg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hτσ _ (K_star h₁), map_star_star, e]

theorem psi_near_one {lam : Fin n → ℝ} (hlam : IsHCParam lam) {w : S} {τ : Mt → (S →L[ℂ] S)}
    (hτ : IsTau ε (lowK ε lam) τ w) (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) :
    ∀ᶠ g : UJ ε in 𝓝 1, ∀ (a b : Fin n) (x y : H),
      Eab ε a b (fun z => ⟪S.orthogonalProjectionOnto y,
        Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ) (umat g) = (Module.finrank ℂ S : ℂ) *
      Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
        (⟪y, σ (toMK k) (w : H)⟫_ℂ * ⟪σ (toMK k) (w : H), x⟫_ℂ) ∂(muK ε)) (umat g) := by
  have h1 := eventually_UJ (p := fun z => z ∈ U1 ε ∧ Psi ε lam τ w z = ps ε lam τ w z) (psLocal n ε lam S τ w hlam hτ)
  have h2 : Tendsto (fun g : Mt => g.map star) (𝓝 1) (𝓝 1) := by
    have := (Continuous.matrix_map (continuous_id (X := Mt)) (continuous_star (R := ℂ))).tendsto 1
    simpa only [id, map_star_one] using this
  have h3 : Tendsto (fun g : UJ ε => umat g) (𝓝 1) (𝓝 1) := (isClosedEmbeddingMatrix n ε).1.continuous.tendsto 1
  filter_upwards [h3.eventually (h2.eventually h1).eventually_nhds] with g hg a b x y
  rw [← eab_const_mul]
  refine eab_local g.2 (hg.mono fun z hz hzJ => ?_) a b
  obtain ⟨hU, he⟩ := hz (UJ_star hzJ)
  rw [he, ps_entry hτ hτσ hU]

end GlobalTheory.Jet.FormGap
