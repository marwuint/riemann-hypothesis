import Development.WeilBound.CoreStatements.ProjectiveValuations.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions MonObj GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop GlobalTheory.HSApp in

theorem exists_frBor_of_matches (T : TorFlag Xo c) {A : Type} [CommRing A] (q : Sp A ⟶ T.X.YY) (k : T.X.F.J)
    (hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U k) {φ : c.F →+* A} {x : Sp A ⟶ gen T.Y} (hx : q ≫ T.X.π = x ≫ genι T.Y)
    (fr : EigFrame T.Y φ (x ≫ genι T.Y))
    (hfr : ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k q hz hx τ j)).left) (ψ : A →+* CAt σ)
    {y : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : spMap ψ ≫ q = z) (hz' : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr k z hz' Q ∧ FrBor t Q y ∧ ∀ s, t (some s) = 1 := by
  subst e
  let z' : Sp (CAt σ) ⟶ T.X.YY := spMap ψ ≫ q
  have ex : spMap ψ ≫ (x ≫ genι T.Y) = z' ≫ T.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ T.Y.j = z' ≫ T.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ T.Y.j = (GlobalTheory.AllWt.ptF y ≫ T.Y.jQ) ≫ genι T.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ ≫ (x ≫ genι T.Y) := (congrArg (· ≫ genι T.Y) hm.1).trans (Category.assoc _ _ _)
    _ = z' ≫ T.X.π := ex
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec T.Y y hxy τ j = GlobalTheory.FlagMod.frVec T.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← T.X.F.tanPull_vecAt k ψ q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := T.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := GlobalTheory.CompHS.BridgeValue.exists_gen_unit Q y eQ
  let t : Ix D → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  refine ⟨Q, t, hQ, GlobalTheory.FlagMod.frBor_of_frVec (T.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => ?_) (fun _ => hu0), fun _ => rfl⟩
  rw [hv τ j]
  refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j' j • _ = 0
    rw [Matrix.one_apply_ne hj', zero_smul]
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j j • _ = _
    rw [Matrix.one_apply_eq, one_smul]

theorem matches_of_sameLie {Z : Model Xo c (RingHom.id c.F)} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    {fr : EigFrame Z φ (x ≫ genι Z)} {ψ : A →+* ℂ} {y y' : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y)
    (h : SameLie y' y) : Matches fr ψ y' := by
  have e : GlobalTheory.AllWt.ptF y' = GlobalTheory.AllWt.ptF y := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans (h.1.trans (pullback.lift_fst _ _ _).symm)
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨e ▸ hm.1, fun τ i => ?_⟩
  rw [e, h.2 τ i]
  exact hm.2 τ i

theorem chr_of_some {e : Ix D → ℤ} {t : Ix D → (CAt σ)ˣ} (h : ∀ s, t (some s) = 1) :
    chr e t = toC (t none).val ^ e none := by
  classical
  have : (∏ ix, t ix ^ e ix) = t none ^ e none := by
    rw [Fintype.prod_option, Finset.prod_eq_one fun s _ => by rw [h, one_zpow], mul_one]
  exact (congrArg (fun u : (CAt σ)ˣ => toC u.val) this).trans (@Units.val_zpow_eq_zpow_val ℂ _ (t none) (e none))

theorem tendsto_punctured {f : ℂ → ℂ} (h : Tendsto (fun w => f (eTwoPi w)) imTop (𝓝 0)) :
    Tendsto f (𝓝[≠] 0) (𝓝 0) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have t₁ : Tendsto (fun u : ℂ => Complex.log u / (2 * Real.pi * Complex.I)) (𝓝[≠] 0) imTop := by
    refine tendsto_comap_iff.2 ?_
    have h₁ : Tendsto (fun u : ℂ => ‖u‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    have h₂ := (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h₁)).atTop_div_const hπ
    refine h₂.congr fun u => ?_
    have e : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [Function.comp_apply]
    rw [e, ← div_div (Complex.log u), Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.div_ofReal_re, Complex.log_re, neg_div]
  refine (h.comp t₁).congr' (eventually_mem_nhdsWithin.mono fun u hu => ?_)
  simp only [Function.comp_apply, eTwoPi]
  rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]

set_option maxHeartbeats 800000 in

theorem exists_eigFrame_tau (T : TorFlag Xo c) {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)]
    {φ : c.F →+* Γ(T.X.YY, W)} (hφ : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap φ) (k : T.X.F.J)
    (hz : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U k) {x' : Sp Γ(T.X.YY, W) ⟶ T.Y.X} (hx : GlobalTheory.FlagMod.tau hW ≫ T.X.π = x') :
    ∃ fr : EigFrame T.Y φ x', ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k _ hz hx τ j)).left := by
  subst hx
  let A : Type := Γ(T.X.YY, W)
  let K : Type := FractionRing A
  letI : Algebra c.F K := ((algebraMap A K).comp φ).toAlgebra
  let z : Sp K ⟶ T.X.YY := spMap (algebraMap A K) ≫ GlobalTheory.FlagMod.tau hW
  have hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X := by
    intro s _
    let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hs : spMap (algebraMap A K) s = η := by
      refine PrimeSpectrum.ext ?_
      let s' : PrimeSpectrum K := s
      have h0 : s'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      show Ideal.comap (algebraMap A K) s'.asIdeal = ⊥
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)
    obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen
      ⟨_, GlobalTheory.FlagMod.tau_le hW le_rfl (Set.mem_univ η)⟩
    obtain ⟨p', rfl⟩ : p ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hpW
    have hsp : η ⤳ (p' : PrimeSpectrum A) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    show GlobalTheory.FlagMod.tau hW (spMap (algebraMap A K) s) ∈ flagOpen T.X
    rw [hs]
    exact (hsp.map (GlobalTheory.FlagMod.tau hW).continuous).mem_open (flagOpen T.X).isOpen hpO
  have hr : Set.range (z ≫ T.X.π) ⊆ Set.range T.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hO (Set.mem_univ s)
  have hf := IsOpenImmersion.lift_fac T.Y.j (z ≫ T.X.π) hr
  refine GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt E H D l Xo c _ _ T.Y T.X A K φ rfl _ k hz
    (IsOpenImmersion.lift T.Y.j (z ≫ T.X.π) hr) ?_ hf.symm
  rw [← openImmersion_comp_structure_eq_generic T.Y, ← Category.assoc, hf, Category.assoc, Category.assoc]
  exact (congrArg (_ ≫ ·) hφ).trans (Spec.map_comp _ _).symm

end DifferentiableLines
