import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.PrinLevClass

noncomputable section

namespace Formalism.MainNotions.CanonicalTranslateJets

open Formalism.BasicNotions NumberField
open Classical

def overG (D : D7) (w : D.what₂.places.Pl) (i : Fin 2) : Prop :=
  D.what₂.places.resChar w = D.host.g i

instance instFactRes (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

abbrev Cw (D : D7) (w : D.what₂.places.Pl) : Type := ℂ_[D.what₂.places.resChar w]

def InR (D : D7) (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

structure Loc (D : D7) (X : DivX D) where

  iota : ∀ w, D.what₂.LL →+* Cw D w

  iota_int : ∀ w (x : D.what₂.LL), ‖iota w x‖ ≤ 1 ↔ 0 ≤ D.what₂.places.val w x

  piG : Fin 2 → 𝓞 D.host.E
  pibG : Fin 2 → 𝓞 D.host.E
  pib_conj : ∀ i, ((pibG i : 𝓞 D.host.E) : D.host.E) = D.host.conj (piG i : D.host.E)
  piG_K : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piG_norm : ∀ i, piG i * pibG i = (D.host.g i : 𝓞 D.host.E)

  piG_cop : ∀ i, IsCoprime (piG i) (pibG i)

  FA : ℕ → Type
  [instFA : ∀ j, AddCommGroup (FA j)]
  [instFAm : ∀ j, Module D.what₂.LL (FA j)]

  inM : ∀ j, (X.MjH j).V →ₗ[D.what₂.LL] FA j
  inM_inj : ∀ j, Function.Injective (inM j)

  Coef : ℕ → Type
  [instCoef : ∀ j, AddCommGroup (Coef j)]
  [instCoefm : ∀ j, Module D.what₂.LL (Coef j)]

  harm : ∀ j, Submodule D.what₂.LL (Coef j)

  hom : ∀ j, (D.R.GG → ℕ) → Submodule D.what₂.LL (Coef j)
  hom_disj : ∀ j Dg Dg', Dg ≠ Dg' → Disjoint (hom j Dg) (hom j Dg')

  intP : ∀ j, D.what₂.places.Pl → Set (Coef j)

  wt : ∀ j, Submodule D.what₂.LL (Coef j)
  wt_harm : ∀ j, wt j ≤ harm j

  Cls : D.what₂.Tup → ℕ → Type
  [clsFin : ∀ μ j, Fintype (Cls μ j)]

  gam : ∀ μ j, Cls μ j → ℕ
  gam_pos : ∀ μ j h, 0 < gam μ j h

  fval : ∀ μ j, D.what₂.MtL μ j →ₗ[D.what₂.LL] (Cls μ j → wt j)
  fval_inj : ∀ μ j, Function.Injective (fval μ j)

  Lt : ℕ → Type
  latOf : ∀ μ j, Cls μ j → Lt j

  thS : ∀ μ j, Cls μ j → (wt j →ₗ[D.what₂.LL] FA j)

  theta_rec : ∀ μ j, InR D j → ∀ f : D.what₂.MtL μ j, D.what₂.jMt μ j f ∈ D.what₂.Zj μ j →
    ∃ x : (X.MjH j).V, inM j x = ∑ h, ((gam μ j h : D.what₂.LL))⁻¹ • thS μ j h (fval μ j f h) ∧
      X.jM j x = D.what₂.thetaP μ j (D.what₂.jMt μ j f)

  ModG : ∀ j, Fin 2 → Lt j → Type
  [modGrp : ∀ j i La, AddCommGroup (ModG j i La)]
  [modFin : ∀ j i La, Fintype (ModG j i La)]

  card_ModG : ∀ j i La, Fintype.card (ModG j i La) = D.host.g i ^ (D.R.f * D.R.r * D.R.nV)

  datG : ∀ μ j (h : Cls μ j) i, ModG j i (latOf μ j h) → D.what₂.LL

  Pt : ℕ → D.what₂.places.Pl → Type

  ev : ∀ j w, Pt j w → (FA j →ₛₗ[iota w] Cw D w)

  Tor : ∀ j w, Pt j w → Lt j → Type
  [torFin : ∀ j w y La, Fintype (Tor j w y La)]
  [torGrp : ∀ j w y La, AddCommGroup (Tor j w y La)]
  [torMod : ∀ j w y La, Module (𝓞 D.host.E) (Tor j w y La)]
  tor_pi : ∀ j w y La i, overG D w i → ∀ t : Tor j w y La, piG i • t = 0

  chi : ∀ j w y La i, Tor j w y La → ModG j i La → Cw D w
  chi_add : ∀ j w y La i t x x', chi j w y La i t (x + x') = chi j w y La i t x * chi j w y La i t x'
  chi_pow : ∀ j w y La i t x, chi j w y La i t x ^ (D.what₂.places.resChar w) = 1
  chi_addT : ∀ j w y La i t t' x, chi j w y La i (t + t') x = chi j w y La i t x * chi j w y La i t' x

  chi_perf : ∀ j w y La i, overG D w i → ∀ t, (∀ x, chi j w y La i t x = 1) → t = 0
  card_Tor : ∀ j w y La i, overG D w i → Fintype.card (Tor j w y La) = Fintype.card (ModG j i La)

  Sec : ∀ j w, Pt j w → Lt j → Type
  [secGrp : ∀ j w y La, AddCommGroup (Sec j w y La)]
  [secMod : ∀ j w y La, Module (Cw D w) (Sec j w y La)]

  Th : ∀ j w y La, Sec j w y La

  Ut : ∀ j w y La, Tor j w y La → (Sec j w y La →ₗ[Cw D w] Sec j w y La)
  Ut_zero : ∀ j w y La, Ut j w y La 0 = LinearMap.id

  jetSec : ∀ j w y La, Sec j w y La →ₗ[Cw D w] (Coef j →ₛₗ[iota w] Cw D w)

  intS : ∀ j w y La, Set (Sec j w y La)

  al : ∀ j w y La, Tor j w y La → Cw D w

  XiC : ∀ μ j w (y : Pt j w) (h : Cls μ j) i,
    (ModG j i (latOf μ j h) → Cw D w) →ₗ[Cw D w] Sec j w y (latOf μ j h)

  SecG : ∀ j w, Pt j w → Lt j → Type
  [secGGrp : ∀ j w y La, AddCommGroup (SecG j w y La)]
  [secGMod : ∀ j w y La, Module (Cw D w) (SecG j w y La)]

  pull : ∀ j w y La, Sec j w y La →ₗ[Cw D w] SecG j w y La

  jetG : ∀ j w y La, SecG j w y La →ₗ[Cw D w] (Coef j →ₛₗ[iota w] Cw D w)

  intSG : ∀ j w y La, Set (SecG j w y La)

  TG : ∀ j w y La, Tor j w y La → Type
  TG_ne : ∀ j w y La b, Nonempty (TG j w y La b)

  act : ∀ j w y La b, TG j w y La b → (SecG j w y La →ₗ[Cw D w] SecG j w y La)

attribute [instance] Loc.instFA Loc.instFAm Loc.instCoef Loc.instCoefm
  Loc.clsFin Loc.modGrp Loc.modFin Loc.torFin Loc.torGrp Loc.torMod Loc.secGrp Loc.secMod
  Loc.secGGrp Loc.secGMod

variable {D : D7} {X : DivX D}

end Formalism.MainNotions.CanonicalTranslateJets

end
