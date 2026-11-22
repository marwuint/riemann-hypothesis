import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValDelta

theorem exists_gal {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) (χ : HChar E) {n : ℕ} (hn : 0 < n) (hχ : χ.OrderDvd n) :
    ∃ r : G E Ω →* ℂˣ, Continuous r ∧ GlobalTheory.GalToHecke.IsHeckeOf art r χ := by
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab E Ω →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  refine ⟨c.comp (GlobalTheory.HeckeGal.toAb E Ω), hcc.comp continuous_quot_mk, fun x σ hσ => ?_⟩
  show χ.1 x = c (GlobalTheory.HeckeGal.toAb E Ω σ)
  rw [← hσ, hc]

variable {D : D7}

theorem delta_tame (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) : ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.delta i σ ^ 15 = 1 := by
  refine ⟨fun h => ?_, fun A hA σ hσ => ?_⟩
  · have h1 := D.ntw.delta_tame i P hP
    have h2 : Ideal.absNorm P.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
      rwa [Ideal.absNorm_span_natCast] at this
    have h3 : Nat.Coprime (Ideal.absNorm P.asIdeal) 15 := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
      rfl
    have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
  · have h1 := pow_card_eq_one' (x := (⟨D.ntw.delta i σ, σ, hσ, rfl⟩ : (Ine (F := D.host.E) A).map (D.ntw.delta i)))
    rw [D.ntw.delta_15 i P hP A hA] at h1
    exact congrArg Subtype.val h1

theorem read_of_side {i : D.ntw.Tw} {b : Bool} {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) (y : D.ntw.O0 i)
    (x : ↥D.LL0) (h : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = (if b then D.ntw.emb0 i else D.ntw.emb0b i) x) :
    e (NX.ofO0 D i k y) = embLL0 D x := by
  rw [← he x, GlobalTheory.SeriesTie.sideEmb, RingHom.comp_apply, ← h]
  simp only [NX.toKk, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem delta_isHeckeOf (cf : CharFrame D) (hR : DeltaRead D cf) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) {i : D.ntw.Tw} {b : Bool} {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) :
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp
      (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) (cf.delAt (D.ntw.l i)) := by
  obtain ⟨n, hn, hord⟩ : ∃ n, 0 < n ∧ (cf.delAt (D.ntw.l i)).OrderDvd n := by
    unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨r, hr, hH⟩ := exists_gal ha _ hn hord
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hc : Continuous ((Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' _ (Subgroup.isOpen_mono (fun g hg => ?_) hker)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  suffices h : (Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r by
    rw [h]; exact hH
  refine GlobalTheory.GalChar.eq_of_frob ha hc hr ?_
  filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero,
    GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
  obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
  have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
    rw [hx, Units.val_inv_eq_inv_val]
  have hrv : r σ = ((cf.delAt (D.ntw.l i)).val v)⁻¹ := by rw [hH.val_eq ha hu hA hσ, inv_inv]
  rw [hrv]
  cases b
  · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
    have h1 := read_of_side he _ x⁻¹ (hd.trans (D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar).symm)
    show Units.map _ ((D.ntw.delta i σ)⁻¹) = _
    rw [map_inv, inv_inj]
    apply Units.ext
    refine h1.trans ?_
    show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
    rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
  · apply Units.ext
    exact (read_of_side he _ x hd).trans hx

theorem tameVal_delta (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) {i : D.ntw.Tw} {b : Bool}
    {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) (a : 𝓞 D.host.E)
    (y : D.host.Eˣ) (hu : a ∉ P.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    IsUnitAt P (atFin P y) ∧ e (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then 1 else -1) a).1) =
      (((cf.delAt (D.ntw.l i)).locK P y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have hA : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P.asIdeal ∧ ϖ0 ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P - 1 by omega)
  have hxu : IsUnitAt P (atFin P y) := by
    show Valued.v (((y : D.host.E) : P.adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  refine ⟨hxu, ?_⟩
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    P _ hA ϖ hϖ1 hϖ2 π hπ (atFin P y) a hxu (by simp [atFin, hy])
  obtain ⟨h15, hord⟩ := delta_tame i hP
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep (D.ntw.delta i) P _ 15 (D.ntw.delta_open i) h15
    (fun A hA σ hσ => ⟨1, by rw [pow_one, hord A hA σ hσ]⟩) _ a hu
    (GlobalTheory.TameResRead.tameRep_zpow hA hσI hϖ1 hϖ2 hπ hu hσval _)]
  have h1 := delta_isHeckeOf cf hR ha he _ σ hσart.symm
  have h2 : D.ntw.delta i (σ ^ (if b then (1 : ℤ) else -1)) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ := by
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  rw [h2]
  exact (congrArg Units.val h1).symm

end GlobalTheory.LevCmp.ValDelta
