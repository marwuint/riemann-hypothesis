import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.NoLocalInvariants

noncomputable section

namespace GlobalTheory.LocalInv

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Eig : Type := ∀ w : PlE H, A.LP w → G H.E N.Om → Multiset ℂ

def FrobLift (w : PlE H) (σ : G H.E N.Om) : Prop := IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ

def charRep (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) : G H.E N.Om →* GL (Fin 1) (N.O i) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp χ

def TemperedSizes (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ → ∀ a : A.LP w, A.tempered a →
  ∀ α ∈ eig w a σ, ((normV w : ℕ) : ℝ) ^ (-(((A.lpDim a : ℝ) - 1) / 2)) ≤ ‖α‖ ∧
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((A.lpDim a : ℝ) - 1) / 2)

def EtaType : Prop := A.csd A.etaT ∧ ∀ τ, ∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

def WeightRegular : Prop := ∀ (i : N.Loc) (_ : A.AV i) (τ : H.E →+* ℂ), (A.infWt i τ).Nodup ∧
  ∀ z ∈ A.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((R.nV : ℂ) - 1) / 2

def GoodCuspidal : Prop := ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
  HasParamX N A i x Sig → goodSig N A Sig → IsCuspIso N A Sig

theorem weightRegular_of_ext (B : NBC A) : WeightRegular N A := fun i P τ => by
  rw [B.embAV_inf i P]
  exact B.infW_alg _ _ τ

theorem one_lt_normV (w : PlE H) : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 H.E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card (𝓞 H.E ⧸ w.asIdeal))

theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  have h := one_lt_normV w
  have : (normV w : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  exact_mod_cast this

theorem r_odd (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem r_add_le (R : Ranks) : R.r + 5 ≤ R.t := R.rank_add_five_le

theorem charRep_val (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) (g : G H.E N.Om) :
    ((charRep N i χ g : GL (Fin 1) (N.O i)) : Matrix (Fin 1) (Fin 1) (N.O i)) =
      Matrix.scalar (Fin 1) ((χ g : (N.O i)ˣ) : N.O i) := rfl

theorem chi_apply (i : N.Loc) (k : ℕ) (hk : k < R.t) (g : G H.E N.Om) :
    N.chi i (k + 1) g = N.chi i 1 g * ((eps N i g) ^ k)⁻¹ := by
  rw [N.chi_def i (k + 1) (by omega) (by omega)]
  simp [eps]

theorem eps_cont (i : N.Loc) : Continuous fun g => ((eps N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((eps N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := r_add_le R
    rw [← Units.val_mul, chi_apply N i 1 (by omega)]
    simp
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem iota_eps (i : N.Loc) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    iotaO N A i ((eps N i σ : (N.O i)ˣ) : N.O i) = ((normV w : ℕ) : ℂ) := by
  have h := cycZ_of_isFrob (l := N.l i) hw hB hσ
  have : ((eps N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [this, h]
  simp

theorem galPol_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) :
    galPol A (A.lpSum a b) = galPol A a * galPol A b := by
  unfold galPol
  rw [A.frobEig_sum a b ha hb, Multiset.map_add, Multiset.prod_add]

theorem galPol_tw_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum, galPol_sum N A _ _ ((A.unr_tw _ _).2 ha) ((A.unr_tw _ _).2 hb)]

theorem galPol_tw_zero (w : PlE H) (s : ℝ) : galPol A (A.lpTw (A.lpZero w) s) = 1 := by
  unfold galPol
  rw [A.frobEig_tw _ _ (A.lpZero_unr w), A.frobEig_zero]
  simp

theorem galPol_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, by simpa using galPol_tw_zero N A w s⟩
  | cons k L ih =>
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 ha, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ ((A.unr_tw _ _).2 ha) ih.1, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]

theorem list_coe {α β : Type} (f : α → β) (L : List α) :
    (do let a ← L; pure (f a) : List β) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem galPol_speh (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  have h := galPol_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s
    (do let a ← List.range p.d; pure ((a : ℕ) : ℝ))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [list_coe, List.map_map, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

theorem galPol_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).2 h1), h2 B σ hB hσ]
  simp [iotaO]

theorem part_alg (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by
  refine ⟨A.csd_tw _ _ hη.1 (hB.1 p hp).2.2, (A.ralg_def _).2 fun τ => ?_⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
  obtain ⟨k0, hk0⟩ := hη.2 τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hle : (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ A.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd.pos)
  rw [A.infG_tw _ _ τ s hs]
  refine ⟨(Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle (hW i P τ).1)).map (add_left_injective s), ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  refine ⟨k + k0 + r + t + 1 - d - a, ?_⟩
  rw [Ranks.nV, hr, ht, hd] at hk
  rw [hk0, ha]
  push_cast at hk ⊢
  linear_combination hk

end GlobalTheory.LocalInv
