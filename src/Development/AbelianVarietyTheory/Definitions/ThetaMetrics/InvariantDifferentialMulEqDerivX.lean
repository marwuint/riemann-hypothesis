import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero

noncomputable section

open Formalism.L2.Th1.A ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

universe u v

namespace GlobalTheory.WeierstrassFormal

section Series

open PowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem coeff_inv : constantCoeff (iSer W) = 0 ∧ coeff 1 (iSer W) = -1 :=
  ⟨(iSerSpec R W).1, (iSerSpec R W).2.1⟩

variable (φ : R →+* S)

end Series

section Group

open MvPowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

def formalGroup : FormalGroup R where
  toPowerSeries := fgl W
  zero_constantCoeff := (fglChord R W).2.2.2.2.1
  lin_coeff_X := (fglChord R W).2.2.2.2.2.1
  lin_coeff_Y := (fglChord R W).2.2.2.2.2.2
  assoc := by
    obtain ⟨F, hF, -⟩ := fglGroup R W
    rw [← hF]
    exact F.assoc

@[simp] theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = fgl W := rfl

instance isComm_formalGroup : (formalGroup W).IsComm := ⟨Fgl2.fgl_symm W⟩

theorem subst_X_inv :
    (formalGroup W).toPowerSeries.subst (![PowerSeries.X, iSer W] : Fin 2 → PowerSeries R) = 0 :=
  fglInv R W

variable {σ : Type*}

theorem subst_inv {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    (formalGroup W).toPowerSeries.subst ![s, (iSer W).subst s] = 0 := by
  have h := congrArg (PowerSeries.subst s) (subst_X_inv W)
  rw [PowerSeries.subst, subst_comp_subst_apply (Fgl2.hasSubst_X_iSer W) hs.const,
    ← PowerSeries.coe_substAlgHom hs, map_zero] at h
  rw [← h]
  congr 1
  funext i
  fin_cases i
  · exact (PowerSeries.subst_X hs).symm
  · rfl

instance : Neg ((formalGroup W).Point σ) where
  neg s := ⟨(iSer W).subst s.val,
    IsNilpotent_subst s.prop.const (by
      have := (coeff_inv W).1
      rw [show MvPowerSeries.constantCoeff (iSer W) = 0 from this]
      exact IsNilpotent.zero)⟩

@[simp] theorem neg_val (s : (formalGroup W).Point σ) : (-s).val = (iSer W).subst s.val := rfl

instance addCommGroupPoint : AddCommGroup ((formalGroup W).Point σ) where
  __ := (inferInstance : AddCommMonoid ((formalGroup W).Point σ))
  zsmul := zsmulRec
  neg_add_cancel s := by
    rw [add_comm]
    exact Subtype.ext (subst_inv W s.prop)

theorem map_zsmul (φ : R →+* S) (n : ℤ) : PowerSeries.map φ (zSer W n) = zSer (W.map φ) n :=
  zSerMap R S φ W n

end Group

end GlobalTheory.WeierstrassFormal
