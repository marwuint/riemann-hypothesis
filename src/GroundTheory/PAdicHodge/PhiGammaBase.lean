import Mathlib
import GroundTheory.PAdicHodge.AInfGalois
import GroundTheory.PAdicHodge.AInfXi
import GroundTheory.PAdicHodge.TiltAlgClosed
import GroundTheory.PAdicHodge.TateCpTwist
set_option maxSynthPendingDepth 1

noncomputable section

open WittVector

namespace GroundTheory.PAdicHodge
namespace PhiGamma

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Ob : Type _ := PreTilt (normInteger ℂ_[p]) p

abbrev Cb : Type _ :=
  Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p

abbrev WC : Type _ := WittVector p (Cb p)

instance : IsAlgClosed (Cb p) := isAlgClosed_tilt

variable {p} {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem preTiltMap_congr {f g : ℂ_[p] →+* ℂ_[p]} (hf : ∀ x, ‖f x‖ = ‖x‖) (hg : ∀ x, ‖g x‖ = ‖x‖)
    (h : f = g) : preTiltMap p f hf = preTiltMap p g hg := by
  subst h; rfl

def galTilt (σ : Gal(PadicAlgCl p/K)) : Cb p →+* Cb p :=
  tiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

def galPreTilt (σ : Gal(PadicAlgCl p/K)) : Ob p →+* Ob p :=
  preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

theorem galTilt_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : Ob p) :
    galTilt σ (algebraMap (Ob p) (Cb p) x) = algebraMap (Ob p) (Cb p) (galPreTilt σ x) :=
  tiltMap_algebraMap _ _ x

theorem norm_galTilt (σ : Gal(PadicAlgCl p/K)) (x : Cb p) : ‖galTilt σ x‖ = ‖x‖ :=
  norm_tiltMap _ _ x

theorem galPreTilt_one (x : Ob p) : galPreTilt (1 : Gal(PadicAlgCl p/K)) x = x := by
  have h : (galCp (1 : Gal(PadicAlgCl p/K)) : ℂ_[p] →+* ℂ_[p]) = RingHom.id ℂ_[p] := by
    rw [galCp_one]; rfl
  have key := AInf.preTiltMap_id (K := ℂ_[p]) (p := p) x
  rw [galPreTilt, preTiltMap_congr _ (fun _ => rfl) h]
  exact key

theorem galPreTilt_mul (σ τ : Gal(PadicAlgCl p/K)) (x : Ob p) :
    galPreTilt (σ * τ) x = galPreTilt σ (galPreTilt τ x) := by
  have h : (galCp (σ * τ) : ℂ_[p] →+* ℂ_[p]) =
      (galCp σ : ℂ_[p] →+* ℂ_[p]).comp (galCp τ : ℂ_[p] →+* ℂ_[p]) := by
    rw [galCp_mul]; rfl
  rw [galPreTilt, galPreTilt, galPreTilt, ← RingHom.comp_apply, ← preTiltMap_comp,
    preTiltMap_congr _ (norm_comp_eq (AInf.norm_galCp_toRingHom τ) (AInf.norm_galCp_toRingHom σ)) h]

theorem galTilt_one (x : Cb p) : galTilt (1 : Gal(PadicAlgCl p/K)) x = x := by
  have : galTilt (1 : Gal(PadicAlgCl p/K)) = RingHom.id (Cb p) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Ob p)) (RingHom.ext fun a => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, galTilt_algebraMap, galPreTilt_one,
      RingHom.id_apply]
  rw [this, RingHom.id_apply]

theorem galTilt_mul (σ τ : Gal(PadicAlgCl p/K)) (x : Cb p) :
    galTilt (σ * τ) x = galTilt σ (galTilt τ x) := by
  have : galTilt (σ * τ) = (galTilt σ).comp (galTilt τ) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Ob p)) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, galTilt_algebraMap, galPreTilt_mul]
  rw [this, RingHom.comp_apply]

instance instMulSemiringActionCb : MulSemiringAction Gal(PadicAlgCl p/K) (Cb p) where
  smul σ x := galTilt σ x
  one_smul x := galTilt_one x
  mul_smul σ τ x := galTilt_mul σ τ x
  smul_zero σ := map_zero (galTilt σ)
  smul_add σ := map_add (galTilt σ)
  smul_one σ := map_one (galTilt σ)
  smul_mul σ := map_mul (galTilt σ)

instance instMulSemiringActionOb : MulSemiringAction Gal(PadicAlgCl p/K) (Ob p) where
  smul σ x := galPreTilt σ x
  one_smul x := galPreTilt_one x
  mul_smul σ τ x := galPreTilt_mul σ τ x
  smul_zero σ := map_zero (galPreTilt σ)
  smul_add σ := map_add (galPreTilt σ)
  smul_one σ := map_one (galPreTilt σ)
  smul_mul σ := map_mul (galPreTilt σ)

def galW (σ : Gal(PadicAlgCl p/K)) : WC p →+* WC p := WittVector.map (galTilt σ)

theorem galW_coeff (σ : Gal(PadicAlgCl p/K)) (x : WC p) (n : ℕ) :
    (galW σ x).coeff n = σ • x.coeff n :=
  WittVector.map_coeff _ x n

theorem galW_one (x : WC p) : galW (1 : Gal(PadicAlgCl p/K)) x = x := by
  ext n
  rw [galW_coeff, one_smul]

theorem galW_mul (σ τ : Gal(PadicAlgCl p/K)) (x : WC p) :
    galW (σ * τ) x = galW σ (galW τ x) := by
  ext n
  rw [galW_coeff, galW_coeff, galW_coeff, mul_smul]

instance instMulSemiringActionWC : MulSemiringAction Gal(PadicAlgCl p/K) (WC p) where
  smul σ x := galW σ x
  one_smul x := galW_one x
  mul_smul σ τ x := galW_mul σ τ x
  smul_zero σ := map_zero (galW σ)
  smul_add σ := map_add (galW σ)
  smul_one σ := map_one (galW σ)
  smul_mul σ := map_mul (galW σ)

theorem gal_smul_natCast (σ : Gal(PadicAlgCl p/K)) (n : ℕ) : σ • (n : WC p) = n :=
  map_natCast (galW σ) n

end PhiGamma
end GroundTheory.PAdicHodge
