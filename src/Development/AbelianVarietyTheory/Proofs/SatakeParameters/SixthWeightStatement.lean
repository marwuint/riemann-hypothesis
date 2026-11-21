import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

noncomputable section

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem normV_pos (w : PlE H) : 0 < normV w := by
  have h := GlobalTheory.LocalInv.one_lt_normV w
  have : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem frob_one {w : PlE H} {a : A.LP w} (hu : A.unr a) (hd : A.lpDim a = 1) : ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem eta_frob (hAut : At.TieAut N A) (w : PlE H) : ∃ b, A.frobEig (A.locG A.etaT w) = {b} ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := frob_one (A.etaT_unr w) (A.locG_dim A.etaT w)
  refine ⟨b, hb, (A.tempered_unr _ (A.etaT_unr w)).1 (hAut.2.2.1 w) b ?_⟩
  rw [hb]
  exact Multiset.mem_singleton_self b

theorem norm_first_character_frobenius (hAut : At.TieAut N A) (i : N.Loc) {w : PlE H} (hw : SplitOut N i w)
    (huμ : A.unr (A.locG (A.muC i) w)) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ‖A.iotaQC i (iotaOQ N A i (chi1 N i σ))‖ =
      (normV w : ℝ) ^ (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2) := by
  obtain ⟨hu, hf⟩ := A.chi_mu i w hw
  have e : A.frobEig (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
      {A.iotaQC i (iotaOQ N A i (chi1 N i σ))} := hf B σ hB hσ
  rw [A.frobEig_tw _ _ hu, A.locG_tw] at e
  obtain ⟨m, hm⟩ := frob_one huμ (A.locG_dim (A.muC i) w)
  have hm1 : ‖m‖ = 1 := (A.tempered_unr _ huμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  obtain ⟨b, hb, hb1⟩ := eta_frob hAut w
  obtain ⟨hui, hfi⟩ := A.etaTinv_def w
  have hfi' : A.frobEig (A.locG A.etaTinv w) = {b⁻¹} := by rw [hfi, hb, Multiset.map_singleton]
  have hfe := A.frobEig_char (A.locG (A.muC i) w) (A.locG A.etaTinv w) b⁻¹ huμ hui (A.locG_dim _ w) hfi'
  rw [hfe, hm, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e
  rw [← e, norm_mul, norm_mul, hm1, norm_inv, hb1, inv_one, one_mul, one_mul,
    Complex.norm_natCast_cpow_of_pos (normV_pos w), Complex.ofReal_re]

theorem eps_frob (i : N.Loc) {w : PlE H} (hl : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    A.iotaQC i (iotaOQ N A i ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i)) = (normV w : ℂ) := by
  have hc := cycZ_of_isFrob (F := H.E) (Ω := N.Om) (l := N.l i) (by simpa [placesOver] using hl) hB hσ
  have e1 : ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [e1, hc]
  show A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
    (algebraMap ℤ_[N.l i] (N.O i) ((normV w : ℕ) : ℤ_[N.l i])))) = _
  rw [A.iotaQ_alg i, PadicInt.coe_natCast, map_natCast, map_natCast]

end GlobalTheory.FrobeniusCharacterNorms

namespace GlobalTheory.FrobeniusCharacterNorms

end GlobalTheory.FrobeniusCharacterNorms
