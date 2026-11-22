import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullTopInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionVanishes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltLocusFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSection
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompEmbEqOfFrBor
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepCusp

section Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_ptY_eq {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (h : GenFrEx Xo c) (Z : Comp Xo c)
    {K : Type} [Field K] [Algebra c.F K] (φ φ' : Om Z →ₐ[c.F] K)
    (e : spMap φ.toRingHom ≫ X.ptY (genFr h Z) = spMap φ'.toRingHom ≫ X.ptY (genFr h Z)) : φ = φ' := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagMod.exists_frMap φ (genFr h Z)
  obtain ⟨y', hy'⟩ := GlobalTheory.FlagMod.exists_frMap φ' (genFr h Z)
  rw [X.ptY_frMap hy, X.ptY_frMap hy'] at e
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY y)
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) (X.lies_ptY y).1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY y)
  obtain ⟨t', ht'⟩ := hQ.exists_frBor (e ▸ X.lies_ptY y')
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  exact eq_of_heq (GlobalTheory.Reg.GenericFlagInj.eq_of_frBor h Z Z φ φ' y y' _ hy hy' (g1 _ _ _ _ _ (g2 _ _ _ ht) ht')).2

theorem exists_val_cuspSec {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (h : GenFrEx Xo c) (w : Sp (Om Z) ⟶ Y₀ X Z)
    (hw : w ≫ inc₀ X Z = X.ptY (genFr h Z)) (hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z) (i : (L₀ X Z la).ι)
    (hi : ⊤ ≤ w ⁻¹ᵁ (L₀ X Z la).U i) :
    ∃ T : Om Z, T ≠ 0 ∧ ∀ g : Cusp Z U la, H0.val w i hU hi (cuspSec X Z U la g) = T * genVal Z g.1 := by
  have e₁ : w ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by rw [X.pt_inc]; exact hw
  have hO₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have hk₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) :=
    (le_iff_ptOf_mem _ _).2 (mem_pull.1 ((le_iff_ptOf_mem _ _).1 hi))
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
  have hQ₂ : X.F.ChartFr (i PUnit.unit) (w ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
  have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
  have v₅ : H0.val w i hU hi (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
      (w ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl w i hU hi hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  rw [v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem val_eq_stalk {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    H0.val x i hO hi f = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom (germ i (ptOf x) hy hj f) := by
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm

theorem gapGe_std (Dw : Datum H) : GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_std (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) :=
  map_nsmul (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)) n a

end Geometry

theorem exists_fg_complexPoint (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [Countable K]
    (hfg : (⊤ : IntermediateField K Ω).FG) (L : IntermediateField K Ω) (hL : L = ⊤) :
    ∃ (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ L) ∧
      IntermediateField.adjoin K (A : Set Ω) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ,
        (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧
          ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) := by
  have : Countable Ω := TwoPoint.countable_of_fg _ _ hfg
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨i⟩ := TwoPoint.nonempty_ringHom_complex Ω
  obtain ⟨s, hs⟩ := hfg
  let A : Subalgebra K Ω := Algebra.adjoin K (s : Set Ω)
  exact ⟨i.comp (algebraMap _ _), A, A, ⟨s, rfl⟩, ⟨s, rfl⟩, le_rfl, fun b _ => hL ▸ IntermediateField.mem_top,
    eq_top_iff.2 (hs ▸ IntermediateField.adjoin.mono _ _ _ Algebra.subset_adjoin), fun b _ hb =>
    ⟨i.comp A.val.toRingHom, fun _ => rfl, fun _ => (map_ne_zero i).2 hb, fun y _ h => RingHom.ext fun a => h a a.2⟩⟩

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem gapGe_sub_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hu : ∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      (((dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ u τ a - u τ b) :
    GlobalTheory.HSApp.GapGe (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (u - FlagTan.kap Dw) := by
  intro τ k hk
  have h₁ := hu τ ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
  have h₂ := GlobalTheory.HSApp.gap_kap_le (Dw := Dw) τ hk
  have h₃ := GlobalTheory.CompHS.gap_eq (u τ) (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl
  have h₄ : (FlagTan.dimFlag Dw + 2).choose 2 ≤ (FlagTan.dimFlag Dw + 3) ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2)
  have h₅ : (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) ≤ ((FlagTan.dimFlag Dw + 3) ^ 2 : ℕ) := by
    exact_mod_cast h₄
  rw [GlobalTheory.CompHS.dimFlag_eq] at h₁
  rw [Pi.sub_apply, GlobalTheory.HSApp.gap_sub]
  dsimp only at h₃
  push_cast at h₁ h₂ h₅ ⊢
  linarith

end GlobalTheory.SepCusp
