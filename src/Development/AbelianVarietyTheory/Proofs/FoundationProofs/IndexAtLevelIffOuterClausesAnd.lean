import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

noncomputable section

namespace GlobalTheory.LevelIndexCompare

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

variable (D : D7) (u : D.what₂.Word)

def incl (w : D.what₂.places.Pl) : LT.Sram D u w →ₗ[LT.Ow D w] (D.fm u).ramSub where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def URamStable (v : (D.mem u).A.vT) : Prop :=
  ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)

theorem T_ne_zero : ((D.mem u).A.T : ℂ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem emb_zpow_smul (n : ℤ) (x : LT.Vl D u 0) :
    (D.fm u).emb 0 ((((D.mem u).A.T : D.what₂.LL) ^ n) • x) = (((D.mem u).A.T : ℂ) ^ n) • (D.fm u).emb 0 x := by
  rw [LinearMap.map_smulₛₗ, map_zpow₀, map_natCast]

theorem exists_isScaledU_iff (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) :
    (∃ g, IsScaledU D u w v g) ↔ URamStable D u v := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    refine ⟨(((D.mem u).A.T : D.what₂.LL) ^ (-(D.fm u).bTop ((D.fm u).tauOf w v))) • (g ⟨x, hx⟩ : LT.Vl D u 0),
      (D.fm u).ramSub.smul_mem _ (g ⟨x, hx⟩).2, ?_⟩
    rw [emb_zpow_smul, hg, smul_smul, ← zpow_add₀ (T_ne_zero D u), neg_add_cancel, zpow_zero, one_smul]
  · intro h
    let e : (D.fm u).ramSub →ₛₗ[D.what₂.embLL] LT.Fn D u 0 := ((D.fm u).emb 0).comp (D.fm u).ramSub.subtype
    have he : Function.Injective e := ((D.fm u).emb_inj 0).comp Subtype.val_injective
    let f : LT.Fn D u 0 →ₗ[ℂ] LT.Fn D u 0 :=
      (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • LT.Uop D u 0 v
    have hf : ∀ x, ∃ y, e y = f (e x) := by
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.1 x.2
      refine ⟨⟨(((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v))) • y,
        (D.fm u).ramSub.smul_mem _ hy⟩, ?_⟩
      exact (emb_zpow_smul D u _ y).trans (by rw [hxy]; rfl)
    exact ⟨descend e e he f hf, fun x => descend_spec e e he f hf x⟩

theorem emb_list_prod (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (l : List (D.mem u).A.vT) (hg : ∀ v ∈ l, IsScaledU D u w v (g v)) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((l.map g).prod x : LT.Vl D u 0) =
      (((D.mem u).A.T : ℂ) ^ (l.map fun v => (D.fm u).bTop ((D.fm u).tauOf w v)).sum) •
        (l.foldr (fun v f => (LT.Uop D u 0 v).comp f) LinearMap.id) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hg v List.mem_cons_self,
      ih (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')), map_smul, smul_smul, List.map_cons, List.sum_cons,
      zpow_add₀ (T_ne_zero D u)]
    rfl

theorem emb_pow (G : Module.End D.what₂.LL (D.fm u).ramSub) (c : ℂ) (U : Module.End ℂ (LT.Fn D u 0))
    (h : ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (G x : LT.Vl D u 0) = c • U ((D.fm u).emb 0 (x : LT.Vl D u 0)))
    (n : ℕ) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((G ^ n) x : LT.Vl D u 0) = c ^ n • (U ^ n) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' c, pow_succ' U, Module.End.mul_apply]

theorem mem_Nlam_iff (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (y : LT.Vl D u 0) :
    y ∈ LT.Nlam D u w ↔ ∃ x : LT.Sram D u w,
      y = ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) (incl D u w x) : (D.fm u).ramSub) := by
  have key : ∀ x : (D.fm u).ramSub,
      (D.fm u).emb 0 ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) x : (D.fm u).ramSub) =
        ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
    intro x
    rw [emb_pow D u _ _ (LT.Uprod D u 0 w)
      (emb_list_prod D u w g _ (fun v hv => hg v (Finset.mem_toList.1 hv))), Finset.sum_map_toList,
      ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (D.fm u).emb_inj 0 (hxy.trans (key (incl D u w ⟨x, hx⟩)).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, key _⟩

def IndexWith (bd : D.what₂.places.Pl → ℝ) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    LT.Nlam D u w ≤ LT.Sram D u w ∧
    ∃ l : ℕ, lengthN_vw D u w = (l : ℕ∞) ∧ (l : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * bd w

theorem indexAtLevelQuoted_iff : IndexAtLevelKnown D u ↔ IndexWith D u (boundQuoted_vp D u) := Iff.rfl

end GlobalTheory.LevelIndexCompare

end
