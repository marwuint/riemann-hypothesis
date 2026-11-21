import Mathlib

open scoped IntermediateField
open scoped Classical

namespace UpperTheory.Reformulated.B.JumpSetsAlt

noncomputable def HypOdd : ℕ → ℕ → Prop :=
  fun q d ↦ Nat.Prime q ∧ Nat.Prime d ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2

noncomputable def IsLayer.{u_1} :
    ℕ → ℕ → ℕ → {L : Type u_1} → [inst : Field L] → [Algebra ℚ L] → L → L → L → Prop :=
  fun n q d {L} [Field L] [Algebra ℚ L] ζ a b ↦
    IsPrimitiveRoot ζ (2 ^ n) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧ ℚ⟮ζ, a, b⟯ = ⊤

noncomputable def E0.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → L → IntermediateField ℚ L :=
  fun {L} [Field L] [Algebra ℚ L] a b ↦ ℚ⟮a, b⟯

noncomputable def F1.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → IntermediateField ℚ L :=
  fun {L} [Field L] [Algebra ℚ L] ζ ↦ ℚ⟮ζ + ζ⁻¹⟯

noncomputable def hostE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] →
      L → L → L → IntermediateField ℚ L :=
  fun {L} [Field L] [Algebra ℚ L] ζ a b ↦ E0 a b ⊔ F1 ζ

theorem aux6 :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      CharZero (hostE ζ a b) := by
  intro L _ _ ζ a b
  infer_instance

theorem aux7 :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L], IsScalarTower ℚ ℚ L := by
  intro L _ _
  infer_instance

@[reducible] noncomputable def G0 : Type := ℤˣ × ℤˣ

@[reducible] noncomputable def HGrp : ℕ → Type :=
  fun e ↦ (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)

@[reducible] noncomputable def GG : ℕ → Type :=
  fun e ↦ G0 × HGrp e

noncomputable def sgn.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → Gal(L/ℚ) → L → ℤˣ :=
  fun {L} [Field L] [Algebra ℚ L] σ x ↦ if σ x = x then 1 else -1

theorem algebra_smulCommClass_complex.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L),
      a ∈ hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_left : E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

noncomputable def aE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨a, algebra_smulCommClass_complex ζ a b⟩ : ↥(hostE ζ a b))

theorem sign_action_map_comm.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L),
      b ∈ hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_left : E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

noncomputable def bE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨b, sign_action_map_comm ζ a b⟩ : ↥(hostE ζ a b))

theorem complex_normed_instance_compat.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L),
      ζ + ζ⁻¹ ∈ hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_right : F1 ζ ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

noncomputable def thE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → hostE ζ a b :=
  fun {L} [Field L] [Algebra ℚ L] ζ a b ↦ ⟨ζ + ζ⁻¹, complex_normed_instance_compat ζ a b⟩

noncomputable def hcl (e : ℕ) : (ZMod (2 ^ (e + 2)))ˣ → HGrp e :=
  fun u ↦ ↑u

noncomputable def hPart.{u_1} :
    {L : Type u_1} →
      [inst : Field L] →
        [inst_1 : Algebra ℚ L] → (e : ℕ) → (ζ a b : L) → Gal(↥(hostE ζ a b)/ℚ) → HGrp e :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (e : ℕ) (ζ a b : L) (σ : Gal(↥(hostE ζ a b)/ℚ)) ↦
      if h :
          ∃ (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ),
            (↑((σ : ↥(hostE ζ a b) → ↥(hostE ζ a b)) (thE ζ a b)) : L) =
              ζ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val + ζ⁻¹ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val then
        hcl e (Classical.choose h)
      else (1 : HGrp e)

noncomputable def galE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] →
      (e : ℕ) → (ζ a b : L) → Gal((hostE ζ a b)/ℚ) → GG e :=
  fun {L} [Field L] [Algebra ℚ L] e ζ a b σ ↦
    ((sgn σ (aE ζ a b), sgn σ (bE ζ a b)), hPart e ζ a b σ)

noncomputable def HostGalois : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      IsLayer (e + 2) q d ζ a b →
      IsGalois ℚ (hostE ζ a b) ∧
      Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) ∧
      (∀ (σ τ : Gal((hostE ζ a b)/ℚ)),
        galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ) ∧
      Function.Bijective (galE e ζ a b)

@[reducible] noncomputable def GalL : ℕ → Type :=
  fun n ↦ (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ

noncomputable def galMap.{u_1} :
    {n : ℕ} →
      {L : Type u_1} →
        [inst : Field L] →
          [inst_1 : Algebra ℚ L] → {ζ : L} → IsPrimitiveRoot ζ ((2 : ℕ) ^ n) → L → L → Gal(L/ℚ) → GalL n :=
    fun {n : ℕ} {L : Type u_1} [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ n)) (a b : L)
        (σ : Gal(L/ℚ)) ↦
      ((IsPrimitiveRoot.autToPow ℚ hζ : Gal(L/ℚ) → (ZMod ((2 : ℕ) ^ n))ˣ) σ, sgn σ a,
        sgn σ b)

theorem glEmbMat_one_eq_one :
    ∀ (e q d : ℕ) (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      IsLayer (e + 2) q d ζ a b → IsPrimitiveRoot ζ (2 ^ (e + 2)) := by
  intro e q d L _ _ ζ a b h
  exact h.1

noncomputable def HostGalSpec : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L)
      (h : IsLayer (e + 2) q d ζ a b) (σ : Gal((hostE ζ a b)/ℚ)),
      (↑(σ (aE ζ a b)) : L) = (((galE e ζ a b σ).1.1 : ℤ) : L) * a ∧
      (↑(σ (bE ζ a b)) : L) = (((galE e ζ a b σ).1.2 : ℤ) : L) * b ∧
      (∀ (u : (ZMod (2 ^ (e + 2)))ˣ),
        (galE e ζ a b σ).2 = hcl e u ↔
        (↑(σ (thE ζ a b)) : L) = ζ ^ u.val.val + ζ⁻¹ ^ u.val.val) ∧
      ∀ (τ : Gal(L/ℚ)),
        (∀ (x : hostE ζ a b), (↑(σ x) : L) = τ x) →
        galE e ζ a b σ =
          (((galMap (glEmbMat_one_eq_one e q d L ζ a b h) a b τ).2.1,
            (galMap (glEmbMat_one_eq_one e q d L ζ a b h) a b τ).2.2),
            hcl e (galMap (glEmbMat_one_eq_one e q d L ζ a b h) a b τ).1)

noncomputable def c0 : G0 := (-1, -1)

noncomputable def cc (e : ℕ) : GG e := (c0, 1)

noncomputable def HostConj : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      IsLayer (e + 2) q d ζ a b →
      NumberField.IsCMField (hostE ζ a b) ∧
      ∀ (φ : hostE ζ a b →+* ℂ) (σ : Gal((hostE ζ a b)/ℚ)),
        (∀ (x : hostE ζ a b), φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e

@[reducible] noncomputable def hostF.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] →
    (ζ a b : L) → Subfield (hostE ζ a b) :=
  fun {L} [Field L] [Algebra ℚ L] ζ a b ↦ NumberField.maximalRealSubfield (hostE ζ a b)

noncomputable def HostReal : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      IsLayer (e + 2) q d ζ a b →
      Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) ∧
      ∀ (x : hostE ζ a b),
        (x ∈ hostF ζ a b ↔ ∀ (σ : Gal((hostE ζ a b)/ℚ)), galE e ζ a b σ = cc e → σ x = x) ∧
        (x ∈ hostF ζ a b ↔ (↑x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯)

theorem hostReal_of : HostGalois → HostGalSpec → HostConj → HostReal := by
  intro hG hS hC e q d hqd L _ _ ζ a b hL
  obtain ⟨hgal, hfin, hmul, hbij⟩ := hG e q d hqd L ζ a b hL
  obtain ⟨hCM, hconj⟩ := hC e q d hqd L ζ a b hL
  have hspec := hS e q d hqd L ζ a b hL
  obtain ⟨σ₀, hσ₀⟩ := hbij.2 (cc e)
  have hone : galE e ζ a b 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hfix : ∀ x : hostE ζ a b, x ∈ hostF ζ a b ↔ σ₀ x = x := by
    intro x
    rw [NumberField.mem_maximalRealSubfield_iff]
    constructor
    · intro hx
      obtain ⟨φ⟩ : Nonempty (hostE ζ a b →+* ℂ) := inferInstance
      apply φ.injective
      rw [(hconj φ σ₀).mpr hσ₀ x]
      exact hx φ
    · intro hx φ
      have h := (hconj φ σ₀).mpr hσ₀ x
      rw [hx] at h
      exact h.symm
  have hval : ((1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val = 1 := by
    haveI : Fact (1 < 2 ^ (e + 2)) := ⟨Nat.one_lt_two_pow (by omega)⟩
    rw [Units.val_one, ZMod.val_one]
  have hth : ∀ σ : Gal(hostE ζ a b/ℚ), (galE e ζ a b σ).2 = 1 ↔
      σ (thE ζ a b) = thE ζ a b := by
    intro σ
    have h := (hspec σ).2.2.1 1
    rw [hval, pow_one, pow_one] at h
    exact h.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hab : ∀ σ : Gal(hostE ζ a b/ℚ),
      (↑(σ (aE ζ a b * bE ζ a b)) : L) =
        ((((galE e ζ a b σ).1.1 * (galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := by
    intro σ
    rw [map_mul, IntermediateField.coe_mul, (hspec σ).1, (hspec σ).2.1]
    push_cast
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    have h := hL.2.1
    have hq : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.1.ne_zero
    exact hq (by simpa using h)
  have hb : b ≠ 0 := by
    rintro rfl
    have h := hL.2.2.1
    have hd : (d : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.2.1.ne_zero
    exact hd (by simpa using h)
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have h := Module.finrank_mul_finrank ℚ (hostF ζ a b) (hostE ζ a b)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (hostF ζ a b) (hostE ζ a b),
      hfin, show 2 ^ (e + 2) = 2 ^ (e + 1) * 2 from pow_succ 2 (e + 1)] at h
    exact Nat.eq_of_mul_eq_mul_right two_pos h
  · rw [hfix]
    exact ⟨fun hx σ hσ => by rw [hbij.1 (hσ.trans hσ₀.symm)]; exact hx, fun hx => hx σ₀ hσ₀⟩
  · set K : IntermediateField ℚ (hostE ζ a b) :=
      ℚ⟮aE ζ a b * bE ζ a b, thE ζ a b⟯ with hK
    have hlift : (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯ ↔ x ∈ K := by
      have h1 := IntermediateField.lift_adjoin ℚ (hostE ζ a b)
        {aE ζ a b * bE ζ a b, thE ζ a b}
      rw [Set.image_pair] at h1
      have h2 := IntermediateField.mem_lift (F := hostE ζ a b)
        (E := ℚ⟮aE ζ a b * bE ζ a b, thE ζ a b⟯) x
      exact (SetLike.ext_iff.mp h1 (x : L)).symm.trans h2
    rw [hlift, hfix]
    constructor
    · intro hx
      rw [← IsGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      have h1 := hab σ
      rw [hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp))] at h1
      have h2 := (hth σ).mpr (hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp)))
      have h3 : (galE e ζ a b σ).1.1 * (galE e ζ a b σ).1.2 = 1 := by
        have h4 : a * b = ((((galE e ζ a b σ).1.1 *
          (galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := h1
        have h5 := (right_eq_mul₀ (mul_ne_zero ha hb)).mp h4
        exact Units.ext (Int.cast_injective (α := L) (by simpa using h5))
      have h6 : galE e ζ a b σ = 1 ∨ galE e ζ a b σ = cc e := by
        generalize galE e ζ a b σ = g at h2 h3
        obtain ⟨⟨s, t⟩, u⟩ := g
        dsimp only at h2 h3
        subst h2
        rcases Int.units_eq_one_or s with rfl | rfl
        · left
          rw [one_mul] at h3
          rw [h3]
          rfl
        · right
          have : t = -1 := by
            rw [neg_mul, one_mul, neg_eq_iff_eq_neg] at h3
            exact h3
          rw [this]
          rfl
      rcases h6 with h6 | h6
      · rw [hbij.1 (h6.trans hone.symm)]
        rfl
      · rw [hbij.1 (h6.trans hσ₀.symm)]
        exact hx
    · intro hx
      have hle : K ≤ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
        rw [hK, IntermediateField.adjoin_le_iff]
        have hgen : ∀ y, σ₀ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
          intro y hy
          rw [IntermediateField.mem_fixedField_iff, Subgroup.forall_mem_zpowers]
          exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ₀)).mpr hy
        rintro y (rfl | rfl)
        · refine hgen _ (Subtype.ext ?_)
          rw [hab σ₀, hσ₀]
          simp [cc, c0, aE, bE]
        · exact hgen _ ((hth σ₀).mp (by rw [hσ₀]; rfl))
      exact (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) σ₀ (Subgroup.mem_zpowers σ₀)

end UpperTheory.Reformulated.B.JumpSetsAlt
