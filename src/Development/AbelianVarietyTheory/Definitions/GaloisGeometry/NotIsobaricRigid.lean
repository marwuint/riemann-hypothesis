import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj

noncomputable section

namespace GlobalTheory.RowTie.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem sign_ne (ε : ℤˣ) : (0 : ℂ) ∉ ({((ε : ℤ) : ℂ)} : Multiset ℂ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

theorem sign_inv (ε : ℤˣ) : ((ε : ℤ) : ℂ)⁻¹ = ((ε : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

abbrev WDw (N : NData R H what₂) (w : PlE H) : Type := WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

def sg (N : NData R H what₂) (ε : ℤˣ) (w : PlE H) : WDw N w := WD.lpUnr _ {((ε : ℤ) : ℂ)}

theorem sg_spec (N : NData R H what₂) (ε : ℤˣ) (w : PlE H) :
    (sg N ε w).unr ∧ (sg N ε w).frobEig = {((ε : ℤ) : ℂ)} ∧ (sg N ε w).lpDim = 1 :=
  WD.lpUnr_spec _ (sign_ne ε)

theorem sg_mul (N : NData R H what₂) (ε δ : ℤˣ) (w : PlE H) :
    sg N (ε * δ) w = (sg N ε w).lpChar (sg N δ w) := by
  have hu := WD.unr_lpChar _ _ (sg_spec N ε w).1 (sg_spec N δ w).1
  rw [WD.unr_eq_lpUnr _ hu, WD.frobEig_char _ _ _ (sg_spec N ε w).1 (sg_spec N δ w).1 (sg_spec N δ w).2.1,
    (sg_spec N ε w).2.1]
  simp [sg]

set_option synthInstance.maxHeartbeats 400000 in

def wdAut (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) : NAut N where
  LP := WDw N
  lpDim := WD.lpDim
  lpZero := fun _ => WD.lpZero _
  lpSum := WD.lpSum
  lpTw := WD.lpTw
  lpChar := WD.lpChar
  lpUnr := fun _ m => WD.lpUnr _ m
  mono0 := WD.mono0
  unr := WD.unr
  frobEig := WD.frobEig
  tempered := WD.tempered
  inePol := WD.inePol
  items₂ := fun k w a => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab (τ k) (γ k w) a
  lpDim_zero := fun _ => WD.lpDim_zero _
  lpDim_sum := WD.lpDim_sum
  lpDim_tw := WD.lpDim_tw
  lpUnr_spec := fun _ m hm => WD.lpUnr_spec m hm
  unr_sum := WD.unr_sum
  monomial_sum_iff := WD.monomial_sum_iff
  frobEig_sum := fun a b _ _ => WD.frobEig_lpSum a b
  unr_tw := WD.unr_tw
  monomial_twist_iff := WD.monomial_twist_iff
  frobEig_tw := WD.frobEig_tw
  frobEig_char := fun a χ c ha hχ _ => WD.frobEig_char a χ c ha hχ
  lpDim_char := WD.lpDim_char
  unr_char := fun a χ _ => WD.unr_lpChar a χ
  monomial_char_iff := WD.monomial_char_iff
  lpZero_unr := fun _ => WD.lpZero_unr
  frobEig_zero := fun _ => WD.frobEig_zero
  lpSum_zero := WD.lpSum_zero
  lpSum_comm := WD.lpSum_comm
  lpSum_assoc := WD.lpSum_assoc
  lpTw_zero := WD.lpTw_zero
  lpTw_add := WD.lpTw_add
  lpTw_sum := WD.lpTw_sum
  unr_eq_lpUnr := WD.unr_eq_lpUnr
  unr_mono0 := WD.unr_mono0
  frobEig_ne_zero := WD.frobEig_ne_zero
  frobEig_card := fun a _ => WD.card_eig a _
  tempered_unr := WD.tempered_unr
  inePol_sum := WD.inePol_sum
  inePol_tw := WD.inePol_tw
  unr_iff_ine := WD.unr_iff_ine
  inertiaCharpoly_zero := fun k w => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩;
    WD.lab_of_lpDim_eq_zero _ _ (WD.lpDim_zero _)
  inertiaCharpoly_add := fun k w a b => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpSum _ _ a b
  CG := fun a => {_ε : ℤˣ // a = 1}
  csd := fun _ => True
  ralg := fun {a} _ => ∀ _τ : H.E →+* ℂ, ({0} : Multiset ℂ).Nodup ∧
    ∀ z ∈ ({0} : Multiset ℂ), ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => sg N π.1 w
  locG_dim := fun π w => (sg_spec N π.1 w).2.2.trans π.2.symm
  locG_unr_ae := fun π => Filter.Eventually.of_forall fun w => (sg_spec N π.1 w).1
  tw := fun π χ => ⟨π.1 * χ.1, π.2⟩
  locG_tw := fun π χ w => sg_mul N _ _ w
  infG := fun _ _ => {0}
  infG_card := fun π _ => π.2.symm
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    have : (0 : ℂ) = s := Multiset.singleton_inj.1 h
    subst this; simp
  csd_tw := fun _ _ _ _ => trivial
  csd_unr := fun π w w' _ _ _ => ⟨(sg_spec N π.1 w').1, by
    rw [(sg_spec N π.1 w').2.1, (sg_spec N π.1 w).2.1, Multiset.map_singleton, sign_inv]⟩
  etaT := ⟨-1, rfl⟩
  etaTinv := ⟨-1, rfl⟩
  etaT_unr := fun w => (sg_spec N _ w).1
  etaT_inert := fun w _ => by rw [(sg_spec N _ w).2.1]; simp
  etaTinv_def := fun w => ⟨(sg_spec N _ w).1, by
    rw [(sg_spec N _ w).2.1, Multiset.map_singleton, sign_inv]⟩
  etaT_split := fun w w' _ _ a b ha hb => by
    rw [(sg_spec N _ _).2.1, Multiset.singleton_inj] at ha hb
    rw [← ha, ← hb]; simp
  plGw := A₀.plGw
  plGw_over := A₀.plGw_over
  plGw_inj := A₀.plGw_inj
  plGw_nconj := A₀.plGw_nconj
  iotaQ := fun i => isEmptyElim i
  iotaQC := fun i => isEmptyElim i
  iota_LL := fun i => isEmptyElim i
  iotaQ_alg := fun i => isEmptyElim i
  muC := fun i => isEmptyElim i
  muC_csd := fun i => isEmptyElim i
  AV := fun i => isEmptyElim i
  finAV := fun i => isEmptyElim i
  ptV := fun i => isEmptyElim i
  typeV := fun i => isEmptyElim i
  typeV_ne := fun i => isEmptyElim i
  typeV_indep := fun i => isEmptyElim i
  typeV_top := fun i => isEmptyElim i
  pt_surj := fun i => isEmptyElim i
  eig_dim := fun i => isEmptyElim i
  locV := fun i => isEmptyElim i
  satV := fun i => isEmptyElim i
  locV_unr := fun i => isEmptyElim i
  pt_loc := fun i => isEmptyElim i
  infWt := fun i => isEmptyElim i
  locW := fun i => isEmptyElim i
  satW := fun i => isEmptyElim i
  lab_loc := fun i => isEmptyElim i
  wdOf := fun i => isEmptyElim i
  wdOf_dim := fun i => isEmptyElim i
  wdOf_unr := fun i => isEmptyElim i
  wdOf_frob := fun i => isEmptyElim i
  wdOf_ine := fun i => isEmptyElim i
  wdOf_mono0 := fun i => isEmptyElim i
  IsCrysW := fun i => isEmptyElim i
  IsPotCrysW := fun i => isEmptyElim i
  IsdRW := fun i => isEmptyElim i
  jumpsW := fun i => isEmptyElim i
  wdOf_unrL := fun i => isEmptyElim i
  wdOf_mono0L := fun i => isEmptyElim i
  jumpsInf := fun i => isEmptyElim i
  locAutHodgeTateWeightsLevelZero := fun i => isEmptyElim i
  jumpsInf_def := fun i => isEmptyElim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => isEmptyElim i
  chi_mu := fun i => isEmptyElim i
  kFbar := fun i => isEmptyElim i

section Inst

variable (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om)

def tie : WDTie N (wdAut N A₀ τ γ) where
  e := fun _ => Equiv.refl _
  dim := fun _ _ => rfl
  zero := fun _ => rfl
  sum := fun _ _ _ => rfl
  tw := fun _ _ _ => rfl
  char := fun _ _ _ _ => rfl
  mono0 := fun _ _ => Iff.rfl
  unr := fun _ _ => Iff.rfl
  frobEig := fun _ _ _ => rfl
  tempered := fun _ _ => Iff.rfl
  inePol := fun _ _ _ _ => rfl

end Inst

section Laws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

open TensorProduct

theorem char_one (a : WD h) : a.lpChar (WD.lpUnr h {1}) = a := by
  have h1 : WD.lpUnr h {1} = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) := by
    rw [WD.unr_eq_lpUnr (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)) ((WD.unr_mk _).mpr (WDRep.unr_diag _)),
      WD.frobEig_diag]
    simp
  induction a using WD.ind with | hP _ a =>
  rw [h1, WD.lpChar_mk]
  refine WD.sound ⟨(TensorProduct.congr (.refl _ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ _), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

end Laws

section Rigid

variable (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om)

def ev (w : PlE H) (p : (Σ a : ℕ, {_ε : ℤˣ // a = 1}) × ℝ) : ℂ :=
  ((p.1.2.1 : ℤ) : ℂ) * ((normV w : ℕ) : ℂ) ^ ((p.2 : ℝ) : ℂ)

end Rigid

end GlobalTheory.RowTie.Model
