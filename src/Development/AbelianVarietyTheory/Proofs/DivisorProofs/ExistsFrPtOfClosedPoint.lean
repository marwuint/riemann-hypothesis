import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TanLinOfCombLinear
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegralOfFrChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpandAlt

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatDenom

theorem exists_dvd_sum {V ι : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Fintype ι] (d a : ι → V)
    (h : ∑ i, a i * d i ≠ 0) : ∃ i, d i ∣ ∑ i, a i * d i := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    exact h (by rw [h0, Finset.sum_empty])
  have key : ∀ s : Finset ι, s.Nonempty → ∃ i, ∀ j ∈ s, d i ∣ d j := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => exact ⟨a, fun j hj => by rw [Finset.mem_singleton.1 hj]⟩
    | cons a s ha hs ih =>
      obtain ⟨i, hi⟩ := ih
      rcases ValuationRing.dvd_total (d i) (d a) with h1 | h1
      · exact ⟨i, fun j hj => (Finset.mem_cons.1 hj).elim (fun e => e ▸ h1) (hi j)⟩
      · exact ⟨a, fun j hj => (Finset.mem_cons.1 hj).elim (fun e => e ▸ dvd_rfl) fun hj => h1.trans (hi j hj)⟩
  obtain ⟨i, hi⟩ := key _ hne
  exact ⟨i, Finset.dvd_sum fun j hj => Dvd.dvd.mul_left (hi j hj) _⟩

theorem det_mul_eq_sum {V : Type} [CommRing V] {m g : ℕ} (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) :
    (M * C).det = ∑ J : Fin m → Fin g, (∏ i, M i (J i)) * (C.submatrix J id).det := by
  first
  | exact @_root_.GlobalTheory.DeterminantExpansion.det_mul_expand
  | exact _root_.GlobalTheory.DeterminantExpansion.det_mul_expand
  | (apply _root_.GlobalTheory.DeterminantExpansion.det_mul_expand <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantExpansion.det_mul_expand <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantExpansion.det_mul_expand <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantExpansion.det_mul_expand ..)

theorem exists_minor_dvd : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (m g : ℕ) (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) (δ : V), δ ≠ 0 → M * C = δ • (1 : Matrix (Fin m) (Fin m) V) → (∃ I : Fin m → Fin g, (M.submatrix id I).det ∣ δ ^ m) ∧ ∃ J : Fin m → Fin g, (C.submatrix J id).det ∣ δ ^ m := by
  intro V _ _ _ m g M C δ hδ h
  have hd : (M * C).det = δ ^ m := by rw [h, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have h0 : δ ^ m ≠ 0 := pow_ne_zero _ hδ
  constructor
  · have e := det_mul_eq_sum C.transpose M.transpose
    rw [← Matrix.transpose_mul, Matrix.det_transpose, hd] at e
    obtain ⟨I, hI⟩ := exists_dvd_sum _ _ (e ▸ h0)
    refine ⟨I, ?_⟩
    rw [← e] at hI
    rwa [← Matrix.det_transpose]
  · have e := det_mul_eq_sum M C
    rw [hd] at e
    obtain ⟨J, hJ⟩ := exists_dvd_sum _ _ (e ▸ h0)
    exact ⟨J, e ▸ hJ⟩

open GlobalTheory.HartogsUnit in

theorem exists_nat_mul_mem : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A] (a : FractionRing A), (∀ (T : CDVR) (α : A →+* T.V) (ι : FractionRing A →+* T.Fr), Function.Injective α → (∀ x, ι (algebraMap A (FractionRing A) x) = algebraMap T.V T.Fr (α x)) → (∀ n : ℕ, 0 < n → IsUnit (n : T.V)) → ι a ∈ (algebraMap T.V T.Fr).range) → ∃ (m : ℕ) (b : A), 0 < m ∧ algebraMap A (FractionRing A) b = (m : FractionRing A) * a := by
  intro A _ _ _ _ _ a h
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap A (FractionRing A) y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 hy0

  have hmem : ∀ (p : Ideal A) [p.IsPrime] (n : ℕ), algebraMap A (Localization.AtPrime p) y ∣
      algebraMap A (Localization.AtPrime p) (n * x) → ∃ w, toFrac p w =
        (n : FractionRing A) * (algebraMap A (FractionRing A) x / algebraMap A (FractionRing A) y) := by
    rintro p _ n ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have := congrArg (toFrac p) hw
    rw [map_mul (toFrac p), ← RingHom.comp_apply, ← RingHom.comp_apply, toFrac_comp, map_mul, map_natCast] at this
    rw [← mul_div_assoc, this, mul_div_cancel_left₀ _ hyK]
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → ∃ n : ℕ, 0 < n ∧
      algebraMap A (Localization.AtPrime p.asIdeal) y ∣ algebraMap A (Localization.AtPrime p.asIdeal) (n * x) := by
    intro p hp
    let L := Localization.AtPrime p.asIdeal
    haveI : IsDomain L := IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one p.asIdeal hp _
    have hinj : Function.Injective (algebraMap A L) :=
      IsLocalization.injective L p.asIdeal.primeCompl_le_nonZeroDivisors
    have hyL : algebraMap A L y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
    by_cases hn : ∃ n : ℕ, 0 < n ∧ ¬ IsUnit (n : L)
    · obtain ⟨n, hn0, hn⟩ := hn
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
      obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hyL hϖ
      have hd : ϖ ∣ (n : L) := by
        rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
        exact hn
      refine ⟨n ^ k, pow_pos hn0 k, ?_⟩
      rw [hu, map_mul, map_natCast, Nat.cast_pow, Units.mul_left_dvd]
      exact (pow_dvd_pow_of_dvd hd k).mul_right _
    · push_neg at hn
      obtain ⟨T, iT, h1, h2⟩ := GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one A p hp
      have hα : Function.Injective (iT.comp (algebraMap A L)) := h1.comp hinj
      have hα' : Function.Injective ((algebraMap T.V T.Fr).comp (iT.comp (algebraMap A L))) :=
        (IsFractionRing.injective T.V T.Fr).comp hα
      obtain ⟨s, hs⟩ := h T _ (IsFractionRing.lift hα') hα (fun x => IsFractionRing.lift_algebraMap hα' x)
        fun n hn0 => by simpa using (hn n hn0).map iT
      rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
        eq_div_iff ((map_ne_zero_iff _ hα').2 hy0)] at hs
      have hs' : s * iT (algebraMap A L y) = iT (algebraMap A L x) :=
        IsFractionRing.injective T.V T.Fr (by rw [map_mul]; exact hs)
      refine ⟨1, one_pos, ?_⟩
      rw [Nat.cast_one, one_mul]
      rcases ValuationRing.dvd_total (algebraMap A L y) (algebraMap A L x) with h3 | ⟨c, hc⟩
      · exact h3
      · have h4 : iT (algebraMap A L y) * (s * iT c) = iT (algebraMap A L y) * 1 := by
          rw [mul_one, ← mul_assoc, mul_comm _ s, hs', ← map_mul, ← hc]
        have h5 := mul_left_cancel₀ ((map_ne_zero_iff _ h1).2 hyL) h4
        have h6 : IsUnit c := (isUnit_map_iff iT c).1 (IsUnit.of_mul_eq_one_right _ h5)
        rw [hc]
        exact h6.mul_right_dvd.2 dvd_rfl
  choose! n hn0 hn using key
  have hfin : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ y ∈ p.asIdeal}.Finite := by
    refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal)
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {y})).subset ?_)
      fun _ _ _ _ h => PrimeSpectrum.ext h
    rintro _ ⟨p, ⟨hp, hyp⟩, rfl⟩
    refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hyp⟩, fun q ⟨hq, hyq⟩ hqp => ?_⟩
    by_contra hne
    have hlt : q < p.asIdeal := lt_of_le_of_ne hqp fun e => hne e.ge
    have hq0 : (⊥ : Ideal A) < q := bot_lt_iff_ne_bot.2 fun e => hy0 (by
      have := hyq (Ideal.mem_span_singleton_self y); rwa [e, Ideal.mem_bot] at this)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hq0
    rw [hp] at h1
    rw [Ideal.height_bot, zero_add] at h2
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h2 1).trans h1
    exact absurd h3 (by decide)
  refine ⟨∏ p ∈ hfin.toFinset, n p, ?_⟩
  have hm : ((∏ p ∈ hfin.toFinset, n p : ℕ) : FractionRing A) *
      (algebraMap A (FractionRing A) x / algebraMap A (FractionRing A) y) ∈ (algebraMap A (FractionRing A)).range := by
    refine (GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := A) _).mpr fun p _ hp => ?_
    obtain ⟨w, hw⟩ := hmem p (∏ p ∈ hfin.toFinset, n p) (by
      by_cases hyp : y ∈ p
      · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hfin.mem_toFinset.2 ⟨hp, hyp⟩ : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∈ _)
        rw [hk, Nat.cast_mul, mul_right_comm, map_mul]
        exact (hn ⟨p, inferInstance⟩ hp).mul_right _
      · exact (IsLocalization.map_units (Localization.AtPrime p) (⟨y, hyp⟩ : p.primeCompl)).dvd)
    rw [GlobalTheory.mem_primeLocalSubalgebra_iff, ← hw]
    exact toFrac_mem p w
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, Finset.prod_pos fun p hp => hn0 p (hfin.mem_toFinset.1 hp).1, hb⟩

section Tan

open MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}

theorem exists_comb (hv : ∀ i, IsTanAtG t x (v i)) (a : Fin m → S) : ∃ w, IsCombAtG t x v a w :=
  ⟨_, (GlobalTheory.LieMet.isComb_iff (fun i => GlobalTheory.LieMet.tanOf (hv i)) a _).2 rfl⟩

theorem tan_of_comb (hv : ∀ i, IsTanAtG t x (v i)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v a w) : IsTanAtG t x w := by
  rw [GlobalTheory.FlatModel.Proj.eq_of_comb (fun i => GlobalTheory.LieMet.tanOf (hv i)) h]
  exact GlobalTheory.LieMet.isTan_tv _

theorem eig_of_comb (hv : ∀ i, IsTanAtG t x (v i)) {s : 𝓞 E →+* S} (he : ∀ i, IsEigG t s (v i)) {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) : IsEigG t s w := by
  rw [GlobalTheory.FlatModel.Proj.eq_of_comb (fun i => GlobalTheory.LieMet.tanOf (hv i)) h]
  intro b
  have h1 : ∀ i, actR t.act b (GlobalTheory.LieMet.tanOf (hv i)) = s b • GlobalTheory.LieMet.tanOf (hv i) := fun i => by
    rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff]
    exact he i b
  rw [GlobalTheory.ShFam.Pad.Pull.eig_iff]
  simp only [map_sum, map_smul, h1, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem isEigG_push {X' : Scheme.{0}} {t' : SAB H X'} {f : X' ⟶ X} (ν : SABMap t' t f) {x' : Sp S ⟶ X'}
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x')
    (s : 𝓞 E →+* S) : IsEigG t' s w ↔ IsEigG t s (w ≫ ν.φ) := by
  refine ⟨fun h a => ?_, fun h a => ?_⟩
  · rw [Category.assoc, ← ν.act, ← Category.assoc, h a, Category.assoc]
  · apply ν.cart.1.hom_ext
    · rw [Category.assoc, ν.act, ← Category.assoc, h a, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, GlobalTheory.LocM.BaseMdl.epsMul_comp]

theorem comb_vecMul (hv : ∀ i, IsTanAtG t x (v i)) {n : ℕ} {q : Fin n → (Sp (DualNumber S) ⟶ t.G.left)}
    {M : Matrix (Fin n) (Fin m) S} (hM : ∀ i, IsCombAtG t x v (M i) (q i)) {a : Fin n → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x q a w) : IsCombAtG t x v (Matrix.vecMul a M) w := by
  rw [← Matrix.mulVec_transpose]
  exact GlobalTheory.TangentLinear.isCombAtG_mulVec v hv q M.transpose a w hM h

end Tan

end GlobalTheory.FlatDenom

end
