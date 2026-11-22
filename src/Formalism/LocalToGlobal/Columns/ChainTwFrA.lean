import Formalism.LocalToGlobal.Columns.StabilizerMapTopIndexAlt
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem tfa_std_iff {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (x : Sp E (n + 1)) :
    x ∈ stdAt E (n + 1) Q ↔ initL E n x ∈ stdAt E n Q ∧ IntAt Q (x (Fin.last n)) := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact h1 j

def tfaD {n : ℕ} (z : E) (hz : z ≠ 0) : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1) :=
  LinearEquiv.piCongrRight fun i : Fin (n + 1) => if i = Fin.last n then LinearEquiv.smulOfNeZero E E z hz else LinearEquiv.refl E E

theorem tfaD_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    tfaD z hz x i = if i = Fin.last n then z * x i else x i := by
  unfold tfaD
  rw [LinearEquiv.piCongrRight_apply]
  split_ifs with h
  · simp [LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  · rfl

theorem tfaD_symm_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    (tfaD z hz).symm x i = if i = Fin.last n then z⁻¹ * x i else x i := by
  have key : tfaD z hz (fun j => if j = Fin.last n then z⁻¹ * x j else x j) = x := by
    funext j
    rw [tfaD_apply]
    by_cases h : j = Fin.last n
    · subst h
      simp [hz]
    · simp only [h, if_false]
  conv_lhs => rw [← key]
  rw [LinearEquiv.symm_apply_apply]

def tfaExtZ {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact (tfaD z hz).trans (extE f)

theorem tfaZ_spec {SG : Finset (HeightOneSpectrum (𝓞 E))} {ST : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ} (hN : N = n + 1) (pi : 𝓞 E)
    (d : DecoSet E n ∅ SG) (hOk : (d.1.til (ST := ST) pi).Ok) (w : SG) (hw : pi ∉ w.1.asIdeal) (hz : (algebraMap (𝓞 E) E pi) ≠ 0)
    (x : Sp E N) :
    tfaExtZ hN (d.1.liftFr w) (algebraMap (𝓞 E) E pi) hz x ∈ localization₂ w.1.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
      x ∈ stdAt E N w.1 := by
  subst hN
  have hl := Deco.liftFr_spec (d.2.hasLift w)
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N ↔ _
  unfold DecoSet.til
  rw [dif_pos hOk]
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ _
  have hinit : initL E n (tfaD (algebraMap (𝓞 E) E pi) hz x) = initL E n x := by
    funext i
    show tfaD _ hz x (Fin.castSucc i) = x (Fin.castSucc i)
    rw [tfaD_apply, if_neg (Fin.castSucc_ne_last i)]
  have hlast : tfaD (algebraMap (𝓞 E) E pi) hz x (Fin.last n) = algebraMap (𝓞 E) E pi * x (Fin.last n) := by
    rw [tfaD_apply, if_pos rfl]
  rw [mem_localization_tilN, initL_extE, extE_last, hinit, hlast, tfa_std_iff]
  refine and_congr (hl.1 _) ⟨fun h => ?_, fun h => (IntAt.coe w.1 pi).mul h⟩
  have h2 := (xtIntAt_piInv hw).mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hz, one_mul] at h2

end Gen

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (u : Pr.Word)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

variable (sel mu) in
open Classical in

def topFrA (hQS : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∈ SG') : TopFr (R := R) sel mu u hSG where
  fr P d := if h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal then
      tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, hQS P.1 P.2⟩) (algebraMap (𝓞 X.E) X.E (Pr.piT u))
        (fun h0 => h.2 (by rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0; rw [h0]; exact zero_mem _))
    else frameOfY u P.1 (tilR hSG u d)
  spec P d x := by
    by_cases h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal
    · rw [dif_pos h]
      exact tfaZ_spec (N_m_succ R) (Pr.piT u) d h.1 ⟨P.1, hQS P.1 P.2⟩ h.2 _ x
    · rw [dif_neg h]
      exact frameOfY_spec u P.1 (tilR hSG u d) x

end Top

end Formalism.L2.Col.Sc.Fr
