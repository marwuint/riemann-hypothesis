import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyThickCardLeCyclicOrder
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (tops)

noncomputable section
namespace GlobalTheory.LvT.WtSign

theorem m_pos (R : Ranks) : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m

theorem k_pred_lt (R : Ranks) : R.k - 1 < R.k := by have := R.m_add_three_le_k; omega

def uLast {R : Ranks} (P : HCParam R) : ℚ := P.u ⟨R.k - 1, k_pred_lt R⟩

def eFirst {R : Ranks} (P : HCParam R) : ℚ := P.e ⟨0, m_pos R⟩

def SignLaw {R : Ranks} {ι : Type} (hc : ι → HCParam R) (top : ι → Prop) : Prop :=
  (∀ τ, top τ → uLast (hc τ) ≤ -(((R.k : ℚ) - 1) / 2)) ∧ ∀ τ, (R.k : ℚ) / 2 ≤ eFirst (hc τ)

theorem e_ge {R : Ranks} (P : HCParam R) (i : ℕ) (hi : i < R.m) :
    eFirst P + (i : ℚ) * ((R.t : ℚ) + 3) ≤ P.e ⟨i, hi⟩ := by
  induction i with
  | zero => simp [eFirst]
  | succ i ih =>
    have h1 := ih (by omega)
    have h2 := P.gap_eb ⟨i, by omega⟩ hi
    have h3 := P.gap_be ⟨i + 1, hi⟩
    push_cast
    simp only at h2
    linarith

theorem sExp_nonneg {R : Ranks} (P : HCParam R) (h : (R.k : ℚ) / 2 ≤ eFirst P) (i : ℕ) (hi : i < R.m) :
    0 ≤ sExp R (P.e ⟨i, hi⟩) (i + 1) := by
  have h1 := e_ge P i hi
  have h2 : (0 : ℚ) ≤ (i : ℚ) * (R.t : ℚ) := by positivity
  have h3 : (0 : ℚ) ≤ (i : ℚ) := by positivity
  simp only [sExp, Ranks.N, Nat.add_sub_cancel]
  push_cast
  nlinarith

theorem eFirst_ge_of_uLast_le {R : Ranks} (P : HCParam R) (h : uLast P ≤ -(((R.k : ℚ) - 1) / 2)) :
    (R.k : ℚ) / 2 ≤ eFirst P := by
  have h1 := P.u_last_gt (by have := k_pred_lt R; omega) (m_pos R)
  have h2 := P.gap_be ⟨0, m_pos R⟩
  have h3 : (0 : ℚ) ≤ R.t := by positivity
  unfold uLast at h
  unfold eFirst
  linarith

theorem eFirst_ge_of_uLast_nonpos {R : Ranks} (P : HCParam R) (h : uLast P ≤ 0) : (R.k : ℚ) / 2 ≤ eFirst P := by
  have h1 := P.u_last_gt (by have := k_pred_lt R; omega) (m_pos R)
  have h2 := P.gap_be ⟨0, m_pos R⟩
  have h5 : (R.k : ℚ) ≤ R.t := by
    have := R.rank_add_five_le
    exact_mod_cast (by omega : R.k ≤ R.t)
  unfold uLast at h
  unfold eFirst
  linarith

variable {D : D7} {u : D.what₂.Word}

theorem bTop_cast (X : Ch D u) (τ : D.what₂.Tau) :
    (X.fm.bTop τ : ℚ) = -uLast (D.hc τ) - ((D.R.k : ℚ) - 1) / 2 := by
  have hk := k_pred_lt D.R
  have hN : D.R.N 0 = D.R.k := by simp [Ranks.N]
  have h := X.fm.lam_eq 0 (Nat.zero_le _) τ ⟨D.R.N 0 - 1, by omega⟩
  rw [dif_pos (show D.R.N 0 - 1 < D.R.k by omega)] at h
  have e : (⟨D.R.N 0 - 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hk⟩ := Fin.ext (by simp only; omega)
  simp only [e, hcToWeightQ, rhoVec] at h
  rw [D.hcW_last u τ (by omega), Nat.cast_sub (by omega)] at h
  unfold MemberForms.bTop DomWeight.detShift uLast
  rw [dif_pos (D.R.N_pos 0)]
  push_cast at h ⊢
  rw [h, show (D.R.N 0 : ℚ) = D.R.k by exact_mod_cast hN]
  ring

theorem sDiv_cast (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (X.C.sDiv i τ : ℚ) = sExp D.R ((D.hc τ).e ⟨i, hi⟩) (i + 1) := by
  rw [X.C.sDiv_eq i hi τ, D.hcW_e]

theorem wtSigns_iff (X : Ch D u) : TwColumn.WtSigns X ↔ SignLaw D.hc (· ∈ tops D) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ hτ => ?_, fun τ => ?_⟩
    · have h : (0 : ℚ) ≤ (X.fm.bTop τ : ℚ) := by exact_mod_cast h1 τ hτ
      rw [bTop_cast] at h
      linarith
    · have h : (0 : ℚ) ≤ (X.C.sDiv 0 τ : ℚ) := by exact_mod_cast h2 0 (m_pos _) τ
      rw [sDiv_cast X 0 (m_pos _)] at h
      simp only [sExp, Ranks.N, Nat.add_sub_cancel, zero_mul, add_zero] at h
      unfold eFirst
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ hτ => ?_, fun i hi τ => ?_⟩
    · have h : (0 : ℚ) ≤ (X.fm.bTop τ : ℚ) := by
        rw [bTop_cast]
        linarith [h1 τ hτ]
      exact_mod_cast h
    · have h : (0 : ℚ) ≤ (X.C.sDiv i τ : ℚ) := by
        rw [sDiv_cast X i hi]
        exact sExp_nonneg _ (h2 τ) i hi
      exact_mod_cast h

theorem mem_tops (τ : D.what₂.Tau) : τ ∈ tops D ↔ (D.eTau τ : D.R.GG) ∈ D.host.topPlaces := by
  simp [tops, topsOf]

theorem b'_pos (s : Scale) : 0 < s.b' := by
  have := s.one_lt_alt
  unfold Scale.b' Scale.a Scale.b Scale.X'
  positivity

theorem uLast_le (L : SizeData₂ D) (τ : D.what₂.Tau) (hτ : τ ∈ tops D) :
    uLast (D.hc τ) ≤ -(((D.R.k : ℚ) - 1) / 2) := by
  have h1 := (mem_tops τ).1 hτ
  unfold Host.topPlaces at h1
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
  have h2 := (L.top_u τ ⟨t, ht⟩ (by have := k_pred_lt D.R; omega) e.symm).2
  have h3 := L.bT_ge ⟨t, ht⟩
  have h4 := b'_pos L.sc
  have h5 : ((uLast (D.hc τ) : ℚ) : ℝ) ≤ ((-(((D.R.k : ℚ) - 1) / 2) : ℚ) : ℝ) := by
    unfold uLast
    rw [h2]
    push_cast
    linarith
  exact_mod_cast h5

open GlobalTheory.Mem

def BaseSigns (B : Base) : Prop := SignLaw B.hc (· ∈ B.wts.tops)

theorem wtSigns_assemble_iff (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (u : B.Word) (X : Ch (assemble B C W V S N G) u) :
    TwColumn.WtSigns X ↔ BaseSigns B := by
  have e : ∀ τ, τ ∈ tops (assemble B C W V S N G) ↔ τ ∈ B.wts.tops := fun τ =>
    (mem_tops (D := assemble B C W V S N G) τ).trans (B.mem_wts_tops τ).symm
  exact (wtSigns_iff (D := assemble B C W V S N G) X).trans
    (and_congr (forall_congr' fun τ => imp_congr (e τ) Iff.rfl) Iff.rfl)

end GlobalTheory.LvT.WtSign
