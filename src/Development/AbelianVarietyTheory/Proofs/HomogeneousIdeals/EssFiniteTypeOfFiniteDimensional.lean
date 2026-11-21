import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIntegralRatioRingIffMemAdjoin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG valR lbPow LBIso IsProjOver isProper_str)
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TupleCone GlobalTheory.TuplePoint

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TupleNorm

variable {L : Type} [Field L]

theorem isIntegralElem_iff_of_range_eq {o A : Type*} [CommRing o] [Algebra o L] [CommRing A]
    (φ : A →+* L) (S : Subalgebra o L) (h : Set.range φ = S) (a : L) :
    φ.IsIntegralElem a ↔ IsIntegral S a := by
  let ψ : A →+* S := φ.codRestrict S fun x => show φ x ∈ (S : Set L) from h ▸ ⟨x, rfl⟩
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨x, hx⟩ : s.1 ∈ Set.range φ := h ▸ s.2
    exact ⟨x, Subtype.ext hx⟩
  have e : φ = (algebraMap S L).comp ψ := rfl
  constructor
  · rintro ⟨p, hp, hpa⟩
    exact ⟨p.map ψ, hp.map _, by rwa [Polynomial.eval₂_map]⟩
  · rintro ⟨p, hp, hpa⟩
    obtain ⟨q, hq, -, hq'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts p).mpr (Polynomial.map_surjective ψ hψ p)) hp
    exact ⟨q, hq', by rwa [← hq, Polynomial.eval₂_map] at hpa⟩

theorem mem_range_valMap_toNormalization {Y : Scheme.{0}} (f : Sp L ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : ⊤ ≤ f ⁻¹ᵁ V)
    (h' : ⊤ ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V)) (a : L) :
    a ∈ Set.range (valMap f.toNormalization _ h').hom ↔ (valMap f V h).hom.IsIntegralElem a := by
  let := (f.app V).hom.toAlgebra
  have h₀ : ⊤ ≤ 𝟙 (Sp L) ⁻¹ᵁ (f ⁻¹ᵁ V) := h
  let v := (valMap (𝟙 (Sp L)) (f ⁻¹ᵁ V) h₀).hom
  have hv₁ : Function.Injective v := valMap_injective _ h₀
  have hv₂ : Function.Surjective v := fun x =>
    ⟨_, valMap_baseRingHom (o := L) (f := 𝟙 _) ((Category.id_comp _).trans (Spec.map_id _).symm)
      h₀ x⟩
  have e₁ : (valMap f V h).hom = v.comp (f.app V).hom := RingHom.ext fun s => by
    have := valR_comp (𝟙 (Sp L)) f V s
    rwa [Category.id_comp, valR_eq _ _ h, valR_eq _ _ h₀] at this
  have e₂ (s) : (valMap f.toNormalization _ h').hom s =
      v ((f.normalizationObjIso hV).hom.hom s).1 := by
    have := valR_appLE (𝟙 (Sp L)) f.toNormalization (U := f.fromNormalization ⁻¹ᵁ V)
      (V := f ⁻¹ᵁ V) (le_top.trans h') h₀ s
    rw [Category.id_comp, valR_eq _ _ h', valR_eq _ _ h₀, ← f.normalizationObjIso_hom_val hV]
      at this
    exact this.symm
  rw [e₁]
  constructor
  · rintro ⟨s, rfl⟩
    rw [e₂]
    exact RingHom.IsIntegralElem.map ((f.normalizationObjIso hV).hom.hom s).2 v
  · intro ha
    obtain ⟨b, rfl⟩ := hv₂ a
    obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hV).hom).2
      ⟨b, RingHom.IsIntegralElem.of_map hv₁ ha⟩
    exact ⟨s, (e₂ s).trans (congrArg (fun x => v x.1) hs)⟩

variable (o : Type) [CommRing o] [Algebra o L] {r m : ℕ} (t : Fin (r + 1) → L) (ht : t ≠ 0)

abbrev Cl : Scheme.{0} := (point o t ht).image

abbrev clι : Cl o t ht ⟶ PSpace o r := (point o t ht).imageι

abbrev clPoint : Sp L ⟶ Cl o t ht := (point o t ht).toImage

abbrev Nm : Scheme.{0} := (clPoint o t ht).normalization

abbrev nmPoint : Sp L ⟶ Nm o t ht := (clPoint o t ht).toNormalization

abbrev toCl : Nm o t ht ⟶ Cl o t ht := (clPoint o t ht).fromNormalization

abbrev toProj : Nm o t ht ⟶ PSpace o r := toCl o t ht ≫ clι o t ht

abbrev str : Nm o t ht ⟶ Sp o := toProj o t ht ≫ PSpace.str o r

abbrev twist : LB (Nm o t ht) := (O1 o r).pull (toProj o t ht)

theorem nmPoint_toProj : nmPoint o t ht ≫ toProj o t ht = point o t ht := by simp

theorem nmPoint_str : nmPoint o t ht ≫ str o t ht = spMap (algebraMap o L) := by
  rw [← Category.assoc, nmPoint_toProj, point_str]

theorem isIntegral_Nm : IsIntegral (Nm o t ht) := inferInstance

theorem isNormalScheme_Nm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Nm o t ht) :=
  IsNormalScheme.pred _

theorem isAffineOpen_preimage_chart (i : Fin (r + 1)) :
    IsAffineOpen (toProj o t ht ⁻¹ᵁ chart o r i) :=
  (isAffineOpen_chart o r i).preimage _

theorem iSup_preimage_chart :
    ⨆ i : {i // t i ≠ 0}, toProj o t ht ⁻¹ᵁ chart o r i.1 = ⊤ := by
  refine top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := exists_mem_chart o r (toProj o t ht x)
  exact ⟨⟨i, ne_zero_of_le (nmPoint_toProj o t ht)
    (le_preimage_of_mem (W := toProj o t ht ⁻¹ᵁ chart o r i) _ hi) le_rfl⟩, hi⟩

variable {o t ht} in

theorem mem_range_valMap_iff {i : Fin (r + 1)} {W : (Nm o t ht).Opens}
    (hW : W = toProj o t ht ⁻¹ᵁ chart o r i) (h : ⊤ ≤ nmPoint o t ht ⁻¹ᵁ W) (a : L) :
    a ∈ Set.range (valMap (nmPoint o t ht) W h).hom ↔ IsIntegral (ratioRing o t i) a := by
  subst hW
  have h₁ : ⊤ ≤ point o t ht ⁻¹ᵁ chart o r i :=
    (le_point_preimage_iff i).2 (ne_zero_of_le (nmPoint_toProj o t ht) h le_rfl)
  have h₂ : ⊤ ≤ clPoint o t ht ⁻¹ᵁ (clι o t ht ⁻¹ᵁ chart o r i) := by
    rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι]
  refine (mem_range_valMap_toNormalization (clPoint o t ht)
    ((isAffineOpen_chart o r i).preimage (clι o t ht)) h₂ h a).trans
    (isIntegralElem_iff_of_range_eq _ _ ?_ a)
  rw [ratioRing, ← range_valMap_point h₁,
    ← ((clι o t ht).app_surjective _ (isAffineOpen_chart o r i)).range_comp]
  congr 1
  funext s
  have := valR_comp (clPoint o t ht) (clι o t ht) (chart o r i) s
  rw [Scheme.Hom.toImage_imageι, valR_eq _ _ h₁, valR_eq _ _ h₂] at this
  exact this.symm

theorem exists_hom_of_isIntegral {z : Fin (m + 1) → L} (hz : z ≠ 0)
    (c : {i // t i ≠ 0} → Fin (m + 1)) (hc : ∀ i, z (c i) ≠ 0)
    (h : ∀ i k, IsIntegral (ratioRing o t i.1) (z k / z (c i))) :
    ∃ φ : Nm o t ht ⟶ PSpace o m, nmPoint o t ht ≫ φ = point o z hz ∧
      φ ≫ PSpace.str o m = str o t ht ∧
      ∀ i, toProj o t ht ⁻¹ᵁ chart o r i.1 ≤ φ ⁻¹ᵁ chart o m (c i) := by
  have hη (i : {i // t i ≠ 0}) := le_preimage_chart (nmPoint_toProj o t ht) i.2
  choose u hu using fun i k => (mem_range_valMap_iff rfl (hη i) _).2 (h i k)
  exact exists_hom_of_coords _ _ (nmPoint_str o t ht) _ (iSup_preimage_chart o t ht) hη hz c hc u
    fun i k => (valR_eq _ _ (hη i) _).trans (hu i k)

def ratioField : Subfield L :=
  Subfield.closure (Set.range (algebraMap o L) ∪
    Set.range fun p : Fin (r + 1) × Fin (r + 1) => t p.1 / t p.2)

variable {t} in

theorem ratioField_eq {i : Fin (r + 1)} (hi : t i ≠ 0) :
    ratioField o t = Subfield.closure (ratioRing o t i : Set L) := by
  refine le_antisymm (Subfield.closure_le.mpr ?_) (Subfield.closure_le.mpr fun x hx => ?_)
  · have h (k) : t k / t i ∈ Subfield.closure (ratioRing o t i : Set L) :=
      Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨p, rfl⟩)
    · exact Subfield.subset_closure ((ratioRing o t i).algebraMap_mem a)
    · have := div_mem (h p.1) (h p.2)
      rwa [div_div_div_cancel_right₀ hi] at this
  · induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Subfield.subset_closure (Or.inr ⟨(k, i), rfl⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

variable {t} in

theorem isAlgebraic_and_essFiniteType [FiniteDimensional (ratioField o t) L] {i : Fin (r + 1)}
    (hi : t i ≠ 0) :
    Algebra.IsAlgebraic (ratioRing o t i) L ∧ Algebra.EssFiniteType (ratioRing o t i) L := by
  have hK := ratioField_eq o hi
  let : Algebra (ratioRing o t i) (ratioField o t) :=
    ((algebraMap (ratioRing o t i) L).codRestrict (ratioField o t) fun x =>
      hK ▸ Subfield.subset_closure x.2).toAlgebra
  have : IsScalarTower (ratioRing o t i) (ratioField o t) L := .of_algebraMap_eq' rfl
  have : FaithfulSMul (ratioRing o t i) (ratioField o t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h =>
      Subtype.ext (congrArg (fun a : ratioField o t => (a : L)) h)
  have : IsFractionRing (ratioRing o t i) (ratioField o t) := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, ha, b, hb, h⟩ := Subfield.mem_closure_iff.mp (hK.le x.2)
    have e := Subring.closure_eq (ratioRing o t i).toSubring
    exact ⟨⟨a, e.le ha⟩, ⟨b, e.le hb⟩, Subtype.ext h.symm⟩
  have : Algebra.EssFiniteType (ratioRing o t i) (ratioField o t) :=
    .of_isLocalization _ (nonZeroDivisors _)
  exact ⟨(IsFractionRing.comap_isAlgebraic_iff (K := ratioField o t)).mpr inferInstance,
    .comp _ (ratioField o t) _⟩

include ht in

theorem essFiniteType_of_finiteDimensional [FiniteDimensional (ratioField o t) L] :
    Algebra.EssFiniteType o L := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  have := (isAlgebraic_and_essFiniteType o hi).2
  have : Algebra.FiniteType o (ratioRing o t i) := .adjoin_of_finite (Set.finite_range _)
  exact .comp o (ratioRing o t i) L

theorem isIso_stalkMap_nmPoint [FiniteDimensional (ratioField o t) L] (x : Sp L) :
    IsIso ((nmPoint o t ht).stalkMap x) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  have := (isAlgebraic_and_essFiniteType o hi).1
  have h := le_preimage_chart (nmPoint_toProj o t ht) hi
  let := (valMap (nmPoint o t ht) _ h).hom.toAlgebra
  have : FaithfulSMul Γ(Nm o t ht, toProj o t ht ⁻¹ᵁ chart o r i) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (valMap_injective _ h)
  have : IsFractionRing Γ(Nm o t ht, toProj o t ht ⁻¹ᵁ chart o r i) L := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨y, hy, hyx⟩ :=
      (Algebra.IsAlgebraic.isAlgebraic (R := ratioRing o t i) x).exists_integral_multiple
    obtain ⟨a, ha⟩ := (mem_range_valMap_iff rfl h _).2 hyx
    obtain ⟨b, hb⟩ := (mem_range_valMap_iff rfl h _).2 (isIntegral_algebraMap (x := y))
    refine ⟨a, b, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ha, hb, Algebra.smul_def]
    exact (mul_div_cancel_left₀ _ fun h0 => hy (Subtype.ext h0)).symm
  have h1 : IsPreimmersion (Spec.map (valMap (nmPoint o t ht) _ h)) :=
    IsPreimmersion.of_isLocalization (R := Γ(Nm o t ht, toProj o t ht ⁻¹ᵁ chart o r i)) (S := L)
      (nonZeroDivisors _)
  have h2 : IsPreimmersion (nmPoint o t ht) := by
    rw [← specMap_valMap_fromSpec (isAffineOpen_preimage_chart o t ht i) _ h]
    infer_instance
  have hη : nmPoint o t ht x = genericPoint _ := by
    refine IsGenericPoint.eq ?_ (genericPoint_spec _)
    rw [isGenericPoint_def, ← (nmPoint o t ht).denseRange.closure_range]
    congr 1
    ext y
    exact ⟨fun hy => ⟨x, hy.symm⟩, fun ⟨x', hy⟩ => by rw [← hy, Subsingleton.elim x' x]; rfl⟩
  have hf : IsField ((Nm o t ht).presheaf.stalk (nmPoint o t ht x)) := by
    rw [hη]
    exact Field.toIsField (Nm o t ht).functionField
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, (nmPoint o t ht).stalkMap_surjective _⟩
  let := hf.toField
  exact RingHom.injective ((nmPoint o t ht).stalkMap x).hom

theorem exists_isClosedImmersion [IsFinite (toCl o t ht)] {e : ℕ} (he : 0 < e)
    (hv : ∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) {z : Fin (m + 1) → L} (hz : z ≠ 0)
    (hs : Submodule.span o (Set.range z) = piece o t e) (c : Fin (r + 1) → Fin (m + 1))
    (hc : ∀ j, z (c j) = t j ^ e) :
    ∃ φ : Nm o t ht ⟶ PSpace o m, IsClosedImmersion φ ∧ nmPoint o t ht ≫ φ = point o z hz ∧
      φ ≫ PSpace.str o m = str o t ht ∧
      ∀ j, φ ⁻¹ᵁ chart o m (c j) = toProj o t ht ⁻¹ᵁ chart o r j := by
  have hπ := nmPoint_toProj o t ht
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_hom_of_isIntegral o t ht hz (fun i => c i.1)
    (fun i => hc i.1 ▸ pow_ne_zero e i.2) fun i k =>
      hc i.1 ▸ isIntegral_div_of_mem_piece i.1 (hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  have h₄ (j) : φ ⁻¹ᵁ chart o m (c j) = toProj o t ht ⁻¹ᵁ chart o r j := by
    refine le_antisymm (fun x hx => ?_) fun x hx =>
      h₃ ⟨j, ne_zero_of_le hπ (le_preimage_of_mem _ hx) le_rfl⟩ hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 ((iSup_preimage_chart o t ht).ge (Set.mem_univ x))
    have e₁ : pullRatio φ _ (c i.1) (h₃ i) (c j) = pullRatio (toProj o t ht) _ i.1 le_rfl j ^ e :=
      ext_of_dense (nmPoint o t ht) fun h => by
        rw [valR_pow _ _ h, valR_pullRatio h₁ h, valR_pullRatio hπ h, hc, hc, div_pow]
    have e₂ := basicOpen_pullRatio (hi := h₃ i) (j := c j)
    rw [e₁, Scheme.basicOpen_pow _ _ he, basicOpen_pullRatio] at e₂
    exact (e₂.ge ⟨hi, hx⟩).2
  refine ⟨φ, ?_, h₁, h₂, h₄⟩
  have := isProper_str o r
  have := isProper_str o m
  have : IsProper (φ ≫ PSpace.str o m) := by rw [h₂]; infer_instance
  have : IsProper φ := .of_comp φ (PSpace.str o m)
  refine isClosedImmersion_of_cover φ φ.isClosedMap.isClosed_range
    (fun i : {i // t i ≠ 0} => chart o m (c i.1)) (fun i => isAffineOpen_chart o m _)
    (fun i => h₄ i.1 ▸ isAffineOpen_preimage_chart o t ht i.1) (fun i => ?_)
    (by simpa only [h₄] using iSup_preimage_chart o t ht)
  rw [Scheme.Hom.app_eq_appLE, surjective_appLE_chart_iff]
  intro s
  have h : ⊤ ≤ nmPoint o t ht ⁻¹ᵁ (φ ⁻¹ᵁ chart o m (c i.1)) := h₄ i.1 ▸ le_preimage_chart hπ i.2
  have h₅ := (isIntegral_ratioRing_iff_mem_adjoin he hs hv i.2).1
    ((mem_range_valMap_iff (h₄ i.1) h _).1 ⟨s, rfl⟩)
  rw [Algebra.adjoin_range_eq_range_aeval] at h₅
  obtain ⟨p, hp⟩ := h₅
  refine ⟨p, valMap_injective _ h ?_⟩
  rw [valMap_eval₂Hom (by rw [h₂, nmPoint_str]) h]
  simp only [valR_pullRatio h₁ h, hc]
  exact hp

section Dedekind

variable [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L]

theorem isFinite_toCl : IsFinite (toCl o t ht) := by
  have := isProper_str o r
  refine isFinite_fromNormalization_of_genericPoints (o := .of o) _ (clι o t ht ≫ PSpace.str o r)
    (fun x _ => charZero_of_injective_ringHom
      ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).Γevaluation x).hom.injective) fun x _ => ?_
  have h : ((clPoint o t ht ≫ clι o t ht ≫ PSpace.str o r).stalkMap x).hom.EssFiniteType := by
    rw [Scheme.Hom.toImage_imageι_assoc, point_str]
    exact essFiniteType_stalkMap_SpecMap _ (RingHom.essFiniteType_algebraMap.mpr ‹_›) x
  rw [Scheme.Hom.stalkMap_comp] at h
  exact RingHom.EssFiniteType.residueFieldMap (.of_comp _ h)

theorem exists_iso_Cl : ∃ (e : ℕ) (_ : 0 < e) (M : ℕ) (z : Fin (M + 1) → L) (hz : z ≠ 0),
    (∀ j, 0 < j → piece o t (j * e) = piece o t e ^ j) ∧
    Submodule.span o (Set.range z) = piece o t e ∧ (∀ j, t j ^ e ∈ Set.range z) ∧
    ∃ ν : Nm o t ht ≅ Cl o z hz, nmPoint o t ht ≫ ν.hom = clPoint o z hz ∧
      (ν.hom ≫ clι o z hz) ≫ PSpace.str o M = str o t ht ∧
      (∀ j k, z k = t j ^ e →
        (ν.hom ≫ clι o z hz) ⁻¹ᵁ chart o M k = toProj o t ht ⁻¹ᵁ chart o r j) ∧
      ∃ w : LB.Iso (lbPow (twist o t ht) e) ((O1 o M).pull (ν.hom ≫ clι o z hz)), w.IsGen ∧
        ∀ (k : PUnit → Fin (M + 1)) (j : PUnit → PUnit → Fin (r + 1)),
          ⊤ ≤ nmPoint o t ht ⁻¹ᵁ (((O1 o M).pull (ν.hom ≫ clι o z hz)).U k ⊓
            (lbPow (twist o t ht) e).U j) →
          valR (nmPoint o t ht) _ (w.s (k, j)).val =
            t (j PUnit.unit PUnit.unit) ^ e / z (k PUnit.unit) := by
  classical
  have := isFinite_toCl o t ht
  obtain ⟨e, he, hv⟩ := exists_piece_mul_eq_pow o t
  obtain ⟨M, z, c, hs, hc⟩ := exists_spanning_tuple o t e
  have hz : z ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    exact Function.ne_iff.mpr ⟨c i, hc i ▸ pow_ne_zero e hi⟩
  obtain ⟨φ, _, h₁, h₂, h₃⟩ := exists_isClosedImmersion o t ht he hv hz hs c hc
  have := IsSchemeTheoreticallyDominant.of_isDominant (nmPoint o t ht)
  let ν := (asIso (closureToClosed (point o z hz) (nmPoint o t ht) φ h₁)).symm
  have hν : ν.hom ≫ clι o z hz = φ := by simp [ν, IsIso.inv_comp_eq]
  refine ⟨e, he, M, z, hz, hv, hs, fun j => ⟨c j, hc j⟩, ν, by simp [ν, IsIso.comp_inv_eq], ?_⟩
  rw [hν]
  refine ⟨h₂, fun j k hk => ?_,
    exists_iso_lbPow (nmPoint_toProj o t ht) h₁ c hc fun j => (h₃ j).ge⟩
  obtain ⟨φ', -, h₁', -, h₃'⟩ := exists_isClosedImmersion o t ht he hv hz hs (Function.update c j k)
    fun j' => by
      by_cases h : j' = j
      · rw [h, Function.update_self, hk]
      · rw [Function.update_of_ne h, hc]
  rw [ext_of_isDominant (nmPoint o t ht) (h₁.trans h₁'.symm), ← h₃' j, Function.update_self]

theorem isProjOver_str : IsProjOver (str o t ht) := by
  obtain ⟨e, -, M, z, hz, -, -, -, ν, -, h, -⟩ := exists_iso_Cl o t ht
  exact ⟨M, ν.hom ≫ clι o z hz, inferInstance, h⟩

end Dedekind

end GlobalTheory.TupleNorm
