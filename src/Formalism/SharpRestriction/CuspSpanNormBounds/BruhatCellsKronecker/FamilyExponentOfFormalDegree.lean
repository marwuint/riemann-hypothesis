import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaBoundOnBoundary
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

theorem capelliPoly_ofReal {n : ℕ} (lam : Fin n → ℝ) (Y : ℝ) :
    Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (Y : ℂ) = ((∏ s, (Y + lam s) : ℝ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

private theorem prod_Icc_one_eq_prod_fin_succ {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ i : Fin n, f (i.1 + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]
    rfl

theorem cfg_P (D : D7) (τ : D.what₂.Tau) (Y : ℝ) :
    (cfgOf D τ).P Y = ∏ s : Fin D.R.r, (Y + lamS D.R (D.hc τ) s) := by
  unfold Formalism.FourierDecayAlt.Sz.Cfg.P
  rw [prod_Icc_one_eq_prod_fin_succ]
  exact Finset.prod_congr rfl fun s _ => congrArg (Y + ·) (cfg_lam D τ s)

theorem cfg_aeff (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : (cfgOf D τ).aeff = aEff D u τ := by
  have hk := D.R.m_add_three_le_k
  have hv := cfg_v D τ 1 le_rfl (by omega)
  have hD : (cfgOf D τ).Del = (D.s.Del : ℝ) := rfl
  have ha : (cfgOf D τ).a = uOne D u τ 1 := (uOne_one D u τ).symm
  unfold Formalism.FourierDecayAlt.Sz.Cfg.aeff aEff
  rw [hv, hD, ha]
  by_cases h : IsTop D τ
  · have ht : (cfgOf D τ).top = true := (cfg_top_iff D τ).2 h
    rw [if_pos ht, if_pos h]
    rfl
  · have ht : (cfgOf D τ).top = false := (cfg_top_false_iff D τ).2 h
    rw [if_neg (by simp [ht]), if_neg h]

theorem cfg_prodb (D : D7) (τ : D.what₂.Tau) : (cfgOf D τ).prodb = ∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j := rfl

theorem deOf_ne (D : D7) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ∀ w : D.what₂.Word, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 2) (hne : uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1)) :
    deOf D u l ≠ deOf D u' l := by
  intro heq
  apply hne
  have hk : (cfgOf D τ).k = D.R.k := rfl
  rw [← cfg_u D u τ (h5 u) (l + 1) (by omega) (by omega), ← cfg_u D u' τ (h5 u') (l + 1) (by omega) (by omega)]
  have a1 : l + 1 ≠ 1 := by omega
  have a2 : l + 1 ≠ (cfgOf D τ).k := by rw [hk]; omega
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.u, a1, a2, if_false, Nat.add_sub_cancel, heq]

theorem Tr_pos (D : D7) (u : D.what₂.Word) : 0 < Tr D u := by
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem ka_pos_of {D : D7} (hv : 1 ≤ D.host.v) : 0 < D.host.ka := by
  exact div_pos Real.pi_pos (by linarith)

end Formalism.MainNotions.BridgeLemma

end
