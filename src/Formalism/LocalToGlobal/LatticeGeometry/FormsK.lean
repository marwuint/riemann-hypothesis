import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.FormData

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped ComplexOrder

namespace Formalism.L2.Geo

section Abs

variable {K : Type} [Field K] [NumberField K]

def expV (b : ℝ) (e : EReal) : ℝ := if e = ⊤ then 0 else b ^ (-e.toReal)

theorem expV_top (b : ℝ) : expV b ⊤ = 0 := by simp [expV]

theorem expV_coe (b x : ℝ) : expV b (x : EReal) = b ^ (-x) := by simp [expV]

theorem expV_nonneg {b : ℝ} (hb : 0 < b) (e : EReal) : 0 ≤ expV b e := by
  unfold expV; split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos hb _).le

theorem expV_eq_zero {b : ℝ} (hb : 0 < b) {e : EReal} : expV b e = 0 ↔ e = ⊤ := by
  unfold expV; split_ifs with h
  · simp [h]
  · simp [h, (Real.rpow_pos_of_pos hb _).ne']

theorem expV_anti {b : ℝ} (hb : 1 ≤ b) {e e' : EReal} (he : e ≠ ⊥) (h : e ≤ e') : expV b e' ≤ expV b e := by
  induction e' using EReal.rec with
  | bot => exact absurd (le_bot_iff.mp h) he
  | top => rw [expV_top]; exact expV_nonneg (by linarith) e
  | coe y =>
    induction e using EReal.rec with
    | bot => exact absurd rfl he
    | top => exact absurd h (by simp)
    | coe x =>
      rw [expV_coe, expV_coe]
      exact Real.rpow_le_rpow_of_exponent_le hb (by have := EReal.coe_le_coe_iff.mp h; linarith)

theorem expV_add {b : ℝ} (hb : 0 < b) {e e' : EReal} (he : e ≠ ⊥) (he' : e' ≠ ⊥) :
    expV b (e + e') = expV b e * expV b e' := by
  induction e using EReal.rec with
  | bot => exact absurd rfl he
  | top => rw [EReal.top_add_of_ne_bot he', expV_top, zero_mul]
  | coe x =>
    induction e' using EReal.rec with
    | bot => exact absurd rfl he'
    | top => rw [EReal.coe_add_top, expV_top, mul_zero]
    | coe y => rw [← EReal.coe_add, expV_coe, expV_coe, expV_coe, neg_add, Real.rpow_add hb]

theorem expV_min {b : ℝ} (hb : 1 ≤ b) {e e' : EReal} (he : e ≠ ⊥) (he' : e' ≠ ⊥) :
    expV b (min e e') = max (expV b e) (expV b e') := by
  rcases le_total e e' with h | h
  · rw [min_eq_left h, max_eq_left (expV_anti hb he h)]
  · rw [min_eq_right h, max_eq_right (expV_anti hb he' h)]

def nrmP (la : HeightOneSpectrum (𝓞 K)) : ℝ := (Ideal.absNorm la.asIdeal : ℝ)

theorem one_lt_nrmP (la : HeightOneSpectrum (𝓞 K)) : 1 < nrmP la := by
  unfold nrmP
  have h1 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : Ideal.absNorm la.asIdeal ≠ 1 := fun h => la.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)

theorem min_vEK_ne_bot (la : HeightOneSpectrum (𝓞 K)) (a b : K) : min (vEK la a) (vEK la b) ≠ ⊥ := by
  rcases min_choice (vEK la a) (vEK la b) with h | h <;> rw [h] <;> exact vEK_ne_bot la _

def avP (la : HeightOneSpectrum (𝓞 K)) : AbsoluteValue K ℝ where
  toFun a := expV (nrmP la) (vEK la a)
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha, vEK_zero, expV_top]
    show expV (nrmP la) (vEK la (a * b)) = expV (nrmP la) (vEK la a) * expV (nrmP la) (vEK la b)
    rw [vEK_mul la ha, vEK_of_ne la ha,
      expV_add (by linarith [one_lt_nrmP la]) (EReal.coe_ne_bot _) (vEK_ne_bot la b)]
  nonneg' a := expV_nonneg (by linarith [one_lt_nrmP la]) _
  eq_zero' a := by
    show expV (nrmP la) (vEK la a) = 0 ↔ a = 0
    rw [expV_eq_zero (by linarith [one_lt_nrmP la])]
    constructor
    · intro h; by_contra ha; rw [vEK_of_ne la ha] at h; exact EReal.coe_ne_top _ h
    · rintro rfl; exact vEK_zero la
  add_le' a b := by
    show expV (nrmP la) (vEK la (a + b)) ≤ expV (nrmP la) (vEK la a) + expV (nrmP la) (vEK la b)
    have hb := one_lt_nrmP la
    calc expV (nrmP la) (vEK la (a + b)) ≤ expV (nrmP la) (min (vEK la a) (vEK la b)) :=
          expV_anti hb.le (min_vEK_ne_bot la a b) (vEK_add la a b)
      _ = max (expV (nrmP la) (vEK la a)) (expV (nrmP la) (vEK la b)) :=
          expV_min hb.le (vEK_ne_bot la a) (vEK_ne_bot la b)
      _ ≤ _ := max_le_add_of_nonneg (expV_nonneg (by linarith) _) (expV_nonneg (by linarith) _)

theorem adicAbv_apply (la : HeightOneSpectrum (𝓞 K)) (a : K) : avP la a = expV (nrmP la) (vEK la a) := rfl

end Abs

namespace FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
  (P : FormsPkg D G NW CompW algW PtY)

def scalL (j : ℕ) : P.Forms j →ₗ[P.KO] P.KO where
  toFun x := P.scal (x : P.FormsS j)
  map_add' x y := P.scal_add x y
  map_smul' a x := P.scal_smul a x

def cuspF (j : ℕ) : Submodule P.KO (P.Forms j) := LinearMap.ker (P.scalL j)

theorem mem_cuspF {j : ℕ} (x : P.Forms j) : x ∈ P.cuspF j ↔ P.scal (x : P.FormsS j) = 0 := Iff.rfl

theorem inc_mem_cuspF {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) : P.inc j w F ∈ P.cuspF j :=
  P.scal_incS F

variable {j : ℕ}

theorem amb_alg (a : P.KO) : P.amb (algebraMap P.KO (P.Forms j) a) = algebraMap P.KO (P.Amb j) a := rfl

end FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

open Classical in

structure FormsKPkg (F : ShimFam D G Lev) : Type 1 where

  κs : Lev

  fs : FormsPkg D G (fun j => (datW D κs j).N) (fun j => (F.U (datW D κs j)).Comp)
    (fun j => (F.U (datW D κs j)).alg)
    (fun j p => ((F.U (datW D κs j)).pad.loc p).Pt ((F.U (datW D κs j)).pad.loc p).YY)

  Hb : Type
  [grpHb : Group Hb]
  [act : ∀ j, MulSemiringAction Hb (fs.Forms j)]

  act_smul : ∀ j (h : Hb) (a : fs.KO) (x : fs.Forms j), h • (a • x) = a • (h • x)

  act_wt : ∀ j (h : Hb) (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ∃ F' : fs.Cusp j w, h • fs.inc j w F = fs.inc j w F'

  mv : ∀ j (la : HeightOneSpectrum (𝓞 fs.KO)), Hb → fs.Pt j la → fs.Pt j la

  vAt_act : ∀ j la (h : Hb) (y : fs.Pt j la) (x : fs.Forms j), fs.vAt la y (h • x) = fs.vAt la (mv j la h y) x

  ip : ∀ j, (fs.KO →+* ℂ) → fs.Forms j → fs.Forms j → ℂ
  ip_add_left : ∀ j σ (f f' g : fs.Forms j), f ∈ fs.cuspF j → f' ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ (f + f') g = ip j σ f g + ip j σ f' g
  ip_add_right : ∀ j σ (f g g' : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → g' ∈ fs.cuspF j →
    ip j σ f (g + g') = ip j σ f g + ip j σ f g'
  ip_smul_left : ∀ j σ (a : fs.KO) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ (a • f) g = star (σ a) * ip j σ f g
  ip_smul_right : ∀ j σ (a : fs.KO) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ f (a • g) = σ a * ip j σ f g
  ip_conj : ∀ j σ (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → ip j σ g f = star (ip j σ f g)
  ip_nonneg : ∀ j σ (f : fs.Forms j), f ∈ fs.cuspF j → 0 ≤ (ip j σ f f).re

  ip_inc : ∀ j σ (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ip j σ (fs.inc j w F) (fs.inc j w F) = ((fs.l2NormAlt j w σ F ^ 2 : ℝ) : ℂ)

  ip_orth : ∀ j σ (w w' : WeightFamilies.Wt D j) (F : fs.Cusp j w) (F' : fs.Cusp j w'), w ≠ w' →
    ip j σ (fs.inc j w F) (fs.inc j w' F') = 0
  ip_act : ∀ j σ (h : Hb) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → ip j σ (h • f) (h • g) = ip j σ f g

  supv : ∀ j, (fs.KO →+* ℂ) → fs.Forms j → ℝ
  supv_inc : ∀ j σ (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), supv j σ (fs.inc j w F) = fs.supN j w σ F
  supv_act : ∀ j σ (h : Hb) (u : fs.Forms j), supv j σ (h • u) = supv j σ u
  ip_mul : ∀ j σ (f u : fs.Forms j), f ∈ fs.cuspF j → u ∈ fs.cuspF j →
    (ip j σ (f * u) (f * u)).re ≤ supv j σ u ^ 2 * (ip j σ f f).re

  CmpK : ℕ → Type
  [cmpKFin : ∀ j, Fintype (CmpK j)]

  orbK : ∀ j, (F.U (datW D κs j)).Comp → CmpK j
  orbK_surj : ∀ j, Function.Surjective (orbK j)

  cmpPt : ∀ j la, fs.Pt j la → CmpK j

  prC : ∀ j, CmpK j → fs.cuspF j →ₗ[fs.KO] fs.cuspF j
  prC_sum : ∀ j (x : fs.cuspF j), ∑ c, prC j c x = x
  prC_orth : ∀ j c d (x : fs.cuspF j), c ≠ d → prC j c (prC j d x) = 0

  prC_inc : ∀ j o (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ∃ F' : fs.Cusp j w,
    (prC j o ⟨fs.inc j w F, fs.inc_mem_cuspF F⟩ : fs.Forms j) = fs.inc j w F' ∧
      ∀ c', fs.cmp j w c' F' = if orbK j c' = o then fs.cmp j w c' F else 0
  vAt_prC_self : ∀ j la (y : fs.Pt j la) (x : fs.cuspF j),
    fs.vAt la y (prC j (cmpPt j la y) x : fs.Forms j) = fs.vAt la y (x : fs.Forms j)
  vAt_prC_ne : ∀ j la (y : fs.Pt j la) c (x : fs.cuspF j), c ≠ cmpPt j la y → fs.vAt la y (prC j c x : fs.Forms j) = ⊤
  ip_prC : ∀ j σ c d (f g : fs.cuspF j), c ≠ d → ip j σ (prC j c f : fs.Forms j) (prC j d g : fs.Forms j) = 0

  ip_posDef : ∀ j σ (m : ℕ) (e : Fin m → fs.Forms j), (∀ a, e a ∈ fs.cuspF j) → LinearIndependent fs.KO e →
    (Matrix.of fun a c => ip j σ (e a) (e c)).PosDef

attribute [instance] FormsKPkg.grpHb FormsKPkg.act FormsKPkg.cmpKFin

namespace FormsKPkg

end FormsKPkg

end Formalism.L2.Geo
