import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContModel

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.ContModel.relVol_of_le {W : Type} [AddCommGroup W]
    {W0 A B : AddSubgroup W} (h : B ≤ A) (hB : B.relIndex W0 ≠ 0) :
    _root_.GlobalTheory.HL.relVol W0 A = B.relIndex A * _root_.GlobalTheory.HL.relVol W0 B := by
  unfold _root_.GlobalTheory.HL.relVol
  have h1 := AddSubgroup.relIndex_inf_mul_relIndex W0 B A
  have h2 := AddSubgroup.relIndex_inf_mul_relIndex B W0 A
  have h3 := AddSubgroup.relIndex_inf_mul_relIndex B A W0
  rw [inf_eq_left.mpr h] at h1 h3
  rw [inf_comm W0 B] at h1
  rw [inf_comm W0 A] at h2
  rw [← h3] at hB ⊢
  have hd : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hB
  have hα : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hB
  have key : (W0.relIndex B : ℝ) * B.relIndex A = B.relIndex (A ⊓ W0) * W0.relIndex A := by
    exact_mod_cast h1.trans h2.symm
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * key

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private theorem ncard_image_mk_eq_mul_relIndex_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A)
    {S : Set W} (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  set Ab : AddSubgroup (W ⧸ B) := A.map (QuotientAddGroup.mk' B) with hAb
  set T : Set ((W ⧸ B) ⧸ Ab) :=
    (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S) with hT
  have hpre : (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T =
      (QuotientAddGroup.mk : W → W ⧸ B) '' S := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
      induction y using QuotientAddGroup.induction_on with
      | H w =>
        rw [QuotientAddGroup.eq, hAb, AddSubgroup.mem_map] at hz
        obtain ⟨a, ha, hax⟩ := hz
        have hax' : ((a : W) : W ⧸ B) = -((x : W) : W ⧸ B) + (w : W ⧸ B) := hax
        refine ⟨x + a, hS x hx a ha, ?_⟩
        rw [QuotientAddGroup.mk_add, hax']
        abel
    · intro hy
      exact ⟨y, hy, rfl⟩
  have e1 : Nat.card ((QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T) = Nat.card Ab * Nat.card T :=
    (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet Ab T)).trans (Nat.card_prod _ _)
  have e2 : Nat.card Ab = B.relIndex A := by
    rw [hAb, ← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
      QuotientAddGroup.ker_mk']
  have e3 : ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard = T.ncard := by
    rw [← Set.ncard_image_of_injective T (QuotientAddGroup.quotientQuotientEquivQuotient B A h).injective]
    congr 1
    rw [hT, Set.image_image, Set.image_image]
    rfl
  rw [← hpre, ← Nat.card_coe_set_eq, e1, e2, e3, Nat.card_coe_set_eq, mul_comm]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.ContModel.cont_eq {W : Type} [AddCommGroup W]
    {W0 A : AddSubgroup W} {S : Set W} (hA : _root_.GlobalTheory.HL.GoodSub W0 A S) :
    _root_.GlobalTheory.HL.cont W0 S =
      (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * _root_.GlobalTheory.HL.relVol W0 A := by
  have hS : _root_.GlobalTheory.HL.IsCO W0 S := ⟨A, hA⟩
  rw [_root_.GlobalTheory.HL.cont, dif_pos hS]
  have hA' : _root_.GlobalTheory.HL.GoodSub W0 hS.choose S := hS.choose_spec
  have hB : (A ⊓ hS.choose).relIndex W0 ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hA.1 hA'.1
  rw [_root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hB,
    _root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hB,
    ← mul_assoc, ← mul_assoc]
  congr 1
  exact_mod_cast (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hA'.2.2.1).symm.trans
    (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hA.2.2.1)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in

theorem _root_.GlobalTheory.HL.ContModel.gramT_rmul (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    _root_.GlobalTheory.HL.gramT L Hm (_root_.GlobalTheory.HL.rmul x A) =
      _root_.GlobalTheory.HL.cT L A * _root_.GlobalTheory.HL.gramT L Hm x * A := by
  ext a b
  simp only [_root_.GlobalTheory.HL.gramT, _root_.GlobalTheory.HL.rmul, _root_.GlobalTheory.HL.hf,
    _root_.GlobalTheory.HL.cT, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.cj_mem (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def] at *
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in

theorem _root_.GlobalTheory.HL.ContModel.gramT_thick (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : 𝒪[F]) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (Ω : Set (Fin m → Fin n → E)) (Γ : Matrix (Fin m) (Fin m) E)
    (i : ℕ) (hΩ : ∀ y ∈ Ω, _root_.GlobalTheory.HL.gramT L Hm y = Γ) :
    ∀ x ∈ _root_.GlobalTheory.HL.thick L ϖ Ω i,
      _root_.GlobalTheory.HL.gramT L Hm x ∈ _root_.GlobalTheory.HL.horb L ϖ Γ i := by
  rintro x ⟨y, hy, A, hA, rfl⟩
  exact ⟨A, hA, by rw [_root_.GlobalTheory.HL.ContModel.gramT_rmul, hΩ y hy]⟩

end GlobalTheory.HL.ContModel
