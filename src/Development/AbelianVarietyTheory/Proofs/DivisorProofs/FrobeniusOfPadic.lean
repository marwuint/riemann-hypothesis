import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PsiPhi

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_phiInv' (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p _

theorem phiInv_frobenius' (a : Ainf p O) : phiInv p O (WittVector.frobenius a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_apply_frobenius (PreTilt O p) p _

theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

theorem frobenius_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  have key : (_root_.frobenius (PreTilt O p) p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

def phiInvAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { phiInv p O with commutes' := fun c => phiInv_ofPadic c }

def frobAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { (WittVector.frobenius : Ainf p O →+* Ainf p O) with commutes' := fun c => frobenius_ofPadic c }

end GlobalTheory.DetInv.PsiPhi

namespace GlobalTheory.DetInv

end GlobalTheory.DetInv
