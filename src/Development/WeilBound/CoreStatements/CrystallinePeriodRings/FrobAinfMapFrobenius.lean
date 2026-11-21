import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem frob_injective_of_fac {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E}
    {f : A →+* B} {g : A →+* E} (h : Fac F f g) (hg : Function.Injective g) :
    Function.Injective f := fun x y e => hg (by rw [← h, ← h, e])

theorem frob_fix_padic {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (F : B →+* B)
    (q : ℚ_[l] →+* B) (h : ∀ z : ℤ_[l], F (q (z : ℚ_[l])) = q (z : ℚ_[l])) (x : ℚ_[l]) :
    F (q x) = q x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := F.comp q) (k := q) (RingHom.ext h)) x

theorem frob_map_mul_natCast {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) (x : A) :
    f ((n : A) * x) = (n : B) * f x := by
  rw [map_mul, map_natCast]

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem frob_oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem frob_qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.cB l (algebraMap (AInf ℂ_[l] l)
    (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z)) := by
  apply ιCD_injective
  refine (ιCD_qB _).trans (Eq.trans ?_ (ιCD_cB _).symm)
  rw [cD_apply, ACris.iota_padicInt, frob_oD_apply, AlgHom.commutes]

theorem frob_phi_padicInt (z : ℤ_[l]) :
    ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (IsPerfectoidField.padicIntToWitt l z)) =
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z) := by
  rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]

theorem φB_qB (q : ℚ_[l]) : Per6.φB l (qB l q) = qB l q :=
  frob_fix_padic (Per6.φB l) (qB l) (fun z =>
    (congrArg (Per6.φB l) (frob_qB_coe z)).trans (((φB_cB _).trans
      (congrArg (Per6.cB l) (frob_phi_padicInt z))).trans (frob_qB_coe z).symm)) q

theorem frob_phi_tA : ACris.phi ℂ_[l] l (Per6.tA l) = (l : ACris.ACris ℂ_[l] l) * Per6.tA l :=
  ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))

theorem φB_tB : Per6.φB l (tB l) = (l : Per6.Bcris l) * tB l :=
  ((φB_cB (Per6.tA l)).trans (congrArg (Per6.cB l) frob_phi_tA)).trans
    (frob_map_mul_natCast (Per6.cB l) l (Per6.tA l))

theorem frob_cB_injective : Function.Injective (Per6.cB l) :=
  frob_injective_of_fac (ιCD_fac l) (cD_injective l)

theorem frob_aB_apply (a : Ainf l) : Per6.aB l a =
    Per6.cB l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) :=
  (RingHom.comp_apply _ _ a).trans (RingHom.comp_apply _ _ _)

theorem frob_coeff_tiltMap (xb : OCb l) (k : ℕ) (y : OC l)
    (h : PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    PreTilt.coeff k (Per6.tiltMap l xb) = Ideal.Quotient.mk _ (Per6.intEquiv l y) :=
  (show PreTilt.coeff k (Per6.tiltMap l xb) = Per6.modPEquiv l (PreTilt.coeff k xb) from rfl).trans
    ((congrArg (Per6.modPEquiv l) h).trans rfl)

theorem frob_ainfMap_teich (xb : OCb l) :
    Per6.ainfMap l (WittVector.teichmuller l xb) = WittVector.teichmuller l (Per6.tiltMap l xb) :=
  WittVector.map_teichmuller l _ _

theorem frob_ainfMap_frobenius (a : Ainf l) :
    Per6.ainfMap l (WittVector.frobenius a) = WittVector.frobenius (Per6.ainfMap l a) := by
  ext n
  simp [Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]

theorem frob_phi_ainfMap (a : Ainf l) :
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l (WittVector.frobenius a)) =
      ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) := by
  rw [ACris.phi_algebraMap, frob_ainfMap_frobenius]
  rfl

theorem aB_frobenius (a : Ainf l) : Per6.aB l (WittVector.frobenius a) = Per6.φB l (Per6.aB l a) :=
  ((frob_aB_apply _).trans (congrArg (Per6.cB l) (frob_phi_ainfMap a))).trans
    ((φB_cB _).symm.trans (congrArg (Per6.φB l) (frob_aB_apply a).symm))

end PositivityTheory.LocInh
