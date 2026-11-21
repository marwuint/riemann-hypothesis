import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions

theorem val_O_nonneg (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.O) :
    0 ≤ D.what₂.places.val w (D.what₂.OtoLL y) := by
  rw [D.val_nonneg_iff]
  have h : D.what₂.OtoLL y ∈ integralClosure ℤ D.what₂.LL := (mem_integralClosure_iff _ _).2 (D.O_int y)
  have e := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) (⟨_, h⟩ : 𝓞 D.what₂.LL)
  exact e.le.trans (HeightOneSpectrum.intValuation_le_one _ _)

def laKIdeal {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) : Ideal (𝓞 B.KO) where
  carrier := {x | 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x))}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_lt_of_le (lt_min ha hb) ((D.what₂.places.val w).map_add _ _)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [smul_eq_mul, map_mul, Set.mem_ofPred_eq, AddValuation.map_mul] at *
    exact hx.trans_le (le_add_of_nonneg_left (val_O_nonneg D w _))

theorem mem_laKIdeal {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) (x : 𝓞 B.KO) :
    x ∈ laKIdeal B w ↔ 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x)) := Iff.rfl

def laKOf {D : D7} (B : WeightFamilies.Prov D) (w : D.what₂.places.Pl) : HeightOneSpectrum (𝓞 B.KO) where
  asIdeal := laKIdeal B w
  isPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, mem_laKIdeal]
      simp
    · intro x y hxy
      rw [mem_laKIdeal, map_mul, map_mul, AddValuation.map_mul] at hxy
      by_contra h
      rw [not_or, mem_laKIdeal, mem_laKIdeal, not_lt, not_lt] at h
      have hx := le_antisymm h.1 (val_O_nonneg D w (B.eO x))
      have hy := le_antisymm h.2 (val_O_nonneg D w (B.eO y))
      rw [hx, hy] at hxy
      simp at hxy
  ne_bot := by
    intro h
    have hm : ((D.what₂.places.resChar w : ℕ) : 𝓞 B.KO) ∈ laKIdeal B w := by
      rw [mem_laKIdeal, map_natCast, map_natCast, D.what₂.places.val_resChar]
      exact_mod_cast D.what₂.places.ramIdx_pos w
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hm
    exact (D.what₂.places.resChar_prime w).ne_zero hm

set_option synthInstance.maxHeartbeats 400000 in

structure Core (D : D7) (nch : NChoice D) where
  B : WeightFamilies.Prov D
  P6 : ModuliIntegralCharts.Prov D
  W : WeightAlgebra.Prov D B P6
  sig_le : ∀ d : P6.Dat, min (P6.jj d) (P6.rk d - P6.jj d) ≤ D.R.m
  ka : ∀ j, WeightFamilies.Wt D j
  ka_big : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ i, ((ka j).aP τ i : ℤ) = D.what₂.kaBig j τ i
  ka_small : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ c, ((ka j).aM τ c : ℤ) = -D.what₂.kaSmall j τ (Fin.rev c)
  embK : ∀ (w : LiftErrorLocal.Pl D) (_b : Bool), B.KO →+* FractionRing (D.ntw.O (nch.twI w))
  embK_int : ∀ w b (x : B.KO), 0 ≤ vAdd (laKOf B (LiftErrorLocal.plS nch w b)) x ↔
    embK w b x ∈ (algebraMap (D.ntw.O (nch.twI w)) (FractionRing (D.ntw.O (nch.twI w)))).range
  toFm : ∀ (w : LiftErrorLocal.Pl D) (j : ℕ) (b : Bool), B.Cusp j (ka j) →ₛₗ[embK w b] D.nexp.Fm (nch.twI w) j b
  toFm_li : ∀ w j b, 1 ≤ j → j ≤ D.R.m → ∀ β : Module.Basis (Module.Free.ChooseBasisIndex B.KO (B.Cusp j (ka j))) B.KO
      (B.Cusp j (ka j)),
    LinearIndependent (FractionRing (D.ntw.O (nch.twI w))) (fun a => toFm w j b (β a))
  toFm_sup : ∀ w j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Bsup (nch.twI w) j b =
    Submodule.span (D.ntw.O (nch.twI w)) (toFm w j b '' (B.Mlat j (ka j) : Set (B.Cusp j (ka j))))

private theorem eventually_abs_le_half_add_of_doubling_bounds (x y w : ℚ) (hx : ∃ z : ℤ, x = z) (hy : ∃ z : ℤ, y = z + 1 / 2)
    (hw : ∃ z : ℤ, w = z) (h1 : x < y) (h2 : y < w) : x + 1 ≤ w := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hw
  have h1' : (a : ℚ) < ((b + 1 : ℤ) : ℚ) := by push_cast; linarith
  have h2' : (b : ℚ) < (c : ℚ) := by linarith
  have h1'' : a < b + 1 := by exact_mod_cast h1'
  have h2'' : b < c := by exact_mod_cast h2'
  have h3 : a + 1 ≤ c := by omega
  exact_mod_cast h3

theorem sigPar_step (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) + 1 ≤ DV.sigPar D τ i := by
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dif_pos h1, dif_pos h0]
    exact eventually_abs_le_half_add_of_doubling_bounds ((D.hc τ).v ⟨i + 1, h1⟩) ((D.hc τ).u ⟨i + 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
      ((D.hc τ).v_int ⟨i + 1, h1⟩) ((D.hc τ).u_half ⟨i + 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
      ((D.hc τ).u_gt_v ⟨i + 1, h1⟩) ((D.hc τ).v_gt_u ⟨i, h0⟩)
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hk : 0 < D.R.k := by omega
      have hm : 0 < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb, dif_pos h0]
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, hm⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = 0 by omega)
      rw [e1]
      have hu2 : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        have h5 := (D.hc τ).v_gt_u ⟨i, h0⟩
        have e2 : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = ⟨i + 1, by omega⟩ :=
          Fin.ext (show D.R.k - 1 = i + 1 by omega)
        rw [e2]
        exact h5
      obtain ⟨zb, hzb⟩ := (D.hc τ).b_int ⟨0, hm⟩
      exact eventually_abs_le_half_add_of_doubling_bounds (-(D.hc τ).b ⟨0, hm⟩) ((D.hc τ).u ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
        ⟨-zb, by rw [hzb, Int.cast_neg]⟩ ((D.hc τ).u_half ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
        ((D.hc τ).u_last_gt hk hm) hu2
    · have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb1, dif_neg h0, dif_pos hb0]
      have g1 := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have g2 : ((D.R.t : ℚ) + 3) / 2 ≤
          (D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ - (D.hc τ).e ⟨i - (D.R.k - 1), hb0⟩ :=
        (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ (show i - (D.R.k - 1) + 1 < D.R.m by omega)
      have e : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, by omega⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 by omega)
      rw [e]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  have h := sigPar_step D τ i hi
  unfold DV.aPlusQ
  push_cast
  linarith

theorem aPlusQ_anti (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : b < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ b ≤ DV.aPlusQ D j τ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (aPlusQ_step D j τ (a + d) (by omega)).trans (ih (by omega))

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + (c + 1) < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dif_pos h0, dif_pos hc]
  have g1 := (D.hc τ).gap_be ⟨j + c, h0⟩
  have g2 : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j + (c + 1), hc⟩ - (D.hc τ).e ⟨j + c, h0⟩ :=
    (D.hc τ).gap_eb ⟨j + c, h0⟩ (show j + c + 1 < D.R.m by omega)
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : j + b < D.R.m) :
    DV.aMinusQ D j τ a ≤ DV.aMinusQ D j τ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega)).trans (aMinusQ_step D j τ (a + d) (by omega))

end Formalism.MainNotions.DIV.Inh

end
