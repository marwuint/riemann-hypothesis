import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]

section Witt

variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]

def Tilt.ofPerfect (f : k →+* R ⧸ span {(p : R)}) : k →+* Tilt p R :=
  Perfection.lift p k (ModP R p) f

variable {p} in
theorem Tilt.coeff_ofPerfect (f : k →+* R ⧸ span {(p : R)}) (n : ℕ) (a : k) :
    PreTilt.coeff n (Tilt.ofPerfect p f a) = f ((frobeniusEquiv k p).symm^[n] a) := rfl

def Ainf.ofWitt (f : k →+* R ⧸ span {(p : R)}) : WittVector p k →+* Ainf p R :=
  WittVector.map (Tilt.ofPerfect p f)

variable {p} in
@[simp] theorem Ainf.ofWitt_teichmuller (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Ainf.ofWitt p f (WittVector.teichmuller p a) = Ainf.teich p (Tilt.ofPerfect p f a) :=
  WittVector.map_teichmuller p _ a

omit [Fact ¬IsUnit (p : R)] in

def wittResidueMap (g : WittVector p k →+* R) : k →+* R ⧸ span {(p : R)} :=
  (Ideal.quotientMap _ g (span_natCast_le_comap p g)).comp
    (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom

omit [Fact ¬IsUnit (p : R)] in
variable {p} in
theorem wittResidueMap_coeff_zero (g : WittVector p k →+* R) (x : WittVector p k) :
    wittResidueMap p g (x.coeff 0) = Ideal.Quotient.mk _ (g x) := by
  have : (WittVector.quotientPEquiv (p := p) (k := k)).symm (x.coeff 0) =
      Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change Ideal.quotientMap _ g (span_natCast_le_comap p g) ((WittVector.quotientPEquiv (p := p) (k := k)).symm _) = _
  rw [this, Ideal.quotientMap_mk]

def Ainf.liftWitt (g : WittVector p k →+* R) : WittVector p k →+* Ainf p R :=
  Ainf.ofWitt p (wittResidueMap p g)

variable {p} in

theorem Ainf.theta_liftWitt [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (x : WittVector p k) : Ainf.theta p R (Ainf.liftWitt p g x) = g x := by
  have key (a : k) : PreTilt.untilt (Tilt.ofPerfect p (wittResidueMap p g) a) =
      g (WittVector.teichmuller p a) := by
    refine Perfection.teichmuller_spec fun n => ?_
    refine ⟨g (WittVector.teichmuller p ((frobeniusEquiv k p).symm^[n] a)), ?_, ?_⟩
    · rw [← wittResidueMap_coeff_zero, WittVector.teichmuller_coeff_zero]
      rfl
    · rw [← map_pow, ← map_pow, ← iterate_frobenius,
        Function.RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm k p) n]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : R)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq]
  have := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (span {(p : R)} ^ n)).comp ((Ainf.theta p R).comp (Ainf.liftWitt p g)))
    ((Ideal.Quotient.mk (span {(p : R)} ^ n)).comp g)
    (by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : R)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _)
    (by intro y; simp [Ainf.liftWitt, key])
  exact RingHom.congr_fun this x

end Witt

section FracWitt

variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]

def fracWittLift {B : Type*} [CommRing B] (f : WittVector p k →+* B) (h : IsUnit (p : B)) :
    FractionRing (WittVector p k) →+* B :=
  IsLocalization.lift (M := nonZeroDivisors (WittVector p k)) (g := f) (by
    rintro ⟨x, hx⟩
    obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x (nonZeroDivisors.ne_zero hx)
    change IsUnit (f _)
    rw [map_mul, map_pow, map_natCast]
    exact (h.pow _).mul ((Units.isUnit _).map f))

@[simp] theorem fracWittLift_algebraMap {B : Type*} [CommRing B] (f : WittVector p k →+* B)
    (h : IsUnit (p : B)) (a : WittVector p k) : fracWittLift p f h (algebraMap _ _ a) = f a :=
  IsLocalization.lift_eq _ a

variable {p} in
theorem fracWitt_hom_ext {B : Type*} [CommRing B] {f g : FractionRing (WittVector p k) →+* B}
    (h : ∀ a : WittVector p k, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext h)

def AinfInv.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* AinfInv p R :=
  fracWittLift p ((algebraMap (Ainf p R) (AinfInv p R)).comp (Ainf.liftWitt p g))
    (AinfInv.isUnit_p p)

variable {p} in
@[simp] theorem AinfInv.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    AinfInv.liftFracWitt p g (algebraMap _ _ a) = algebraMap _ _ (Ainf.liftWitt p g a) :=
  fracWittLift_algebraMap p _ _ a

variable {p} in
theorem AinfInv.theta_liftFracWitt [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (a : WittVector p k) :
    AinfInv.theta p R (AinfInv.liftFracWitt p g (algebraMap _ _ a)) = algebraMap R _ (g a) := by
  simp [Ainf.theta_liftWitt]

end FracWitt

variable [IsAdicComplete (span {(p : R)}) R]

variable {p} in

theorem Ainf.theta_algebraMap_padicInt (g : ℤ_[p] →+* R) (a : ℤ_[p]) :
    Ainf.theta p R (algebraMap ℤ_[p] _ a) = g a := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : R)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  have ha : a = (PadicInt.appr a n : ℤ_[p]) + c * (p : ℤ_[p]) ^ n := by rw [hc]; ring
  rw [ha, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simp only [map_add, map_mul, map_pow, map_natCast]
  exact ⟨Ainf.theta p R (algebraMap ℤ_[p] _ c) - g c, by ring⟩

variable {p} in

theorem AinfInv.theta_algebraMap_padic (g : ℤ_[p] →+* R) (j : ℚ_[p] →+* Localization.Away (p : R))
    (hj : ∀ a : ℤ_[p], j (algebraMap _ _ a) = algebraMap R _ (g a)) (x : ℚ_[p]) :
    AinfInv.theta p R (algebraMap ℚ_[p] _ x) = j x :=
  RingHom.congr_fun (padic_hom_ext (f := (AinfInv.theta p R).comp (algebraMap ℚ_[p] _)) (g := j)
    (fun a => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (AinfInv p R), AinfInv.theta_algebraMap,
        Ainf.theta_algebraMap_padicInt g, hj])) x

namespace BdRPlus

variable {p}

variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]

theorem exists_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) :
    ∃ s : L →+* BdRPlus p R, (∀ x, theta p R (s x) = j x) ∧
      ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) := by
  letI : Algebra F (AinfInv p R) := ι.toAlgebra
  let e := RingHom.quotientKerEquivOfSurjective hθ
  let f : L →ₐ[F] AinfInv p R ⧸ AinfInv.kerTheta p R :=
    { e.symm.toRingHom.comp j with
      commutes' := fun a => by
        change e.symm (j (algebraMap F L a)) = Ideal.Quotient.mk _ (ι a)
        rw [RingEquiv.symm_apply_eq, hj]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨g.toRingHom, fun x => ?_, fun a => g.commutes a⟩
  have h1 : AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x) = e.symm (j x) :=
    AlgHom.congr_fun hg x
  change e (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x)) = j x
  rw [h1, RingEquiv.apply_symm_apply]

def «section» [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) : L →+* BdRPlus p R :=
  (exists_section hθ ι j hj).choose

theorem theta_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (x : L) :
    theta p R («section» hθ ι j hj x) = j x := (exists_section hθ ι j hj).choose_spec.1 x

theorem section_algebraMap [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (a : F) :
    «section» hθ ι j hj (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) :=
  (exists_section hθ ι j hj).choose_spec.2 a

end BdRPlus

theorem formallyEtale_of_isAlgebraic (F : Type v) (L : Type w) [Field F] [Field L] [Algebra F L]
    [CharZero F] [Algebra.IsAlgebraic F L] : Algebra.FormallyEtale F L :=
  Algebra.FormallyEtale.of_isSeparable F L

theorem AinfInv.theta_surjective_of_frobenius
    (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (AinfInv.theta p R) := by
  intro y
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (p : R)) y
  obtain ⟨b, rfl⟩ := surjective_fontaineTheta hF a
  obtain ⟨u, hu⟩ := (AinfInv.isUnit_p p (R := R)).pow n
  refine ⟨algebraMap _ _ b * ↑u⁻¹, ?_⟩
  simp only [map_pow, map_natCast] at h
  have h2 : AinfInv.theta p R ↑u = (p : Localization.Away (p : R)) ^ n := by
    rw [hu, map_pow, map_natCast]
  rw [map_mul, AinfInv.theta_algebraMap, Ainf.theta, ← h, ← h2, mul_assoc, ← map_mul,
    Units.mul_inv, map_one, mul_one]

end Reformulated.AutPerF
