import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

theorem AinfInv.kerTheta_le_comap (f : R →+* S) :
    AinfInv.kerTheta p R ≤ (AinfInv.kerTheta p S).comap (AinfInv.map p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, AinfInv.theta_map, RingHom.mem_ker.1 hx, map_zero]

variable {p} in
@[simp] theorem AinfInv.map_algebraMap_padic (f : R →+* S) (a : ℚ_[p]) :
    AinfInv.map p f (algebraMap ℚ_[p] _ a) = algebraMap ℚ_[p] _ a := by
  refine RingHom.congr_fun (padic_hom_ext (f := (AinfInv.map p f).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] (AinfInv p S)) fun b => ?_) a
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (AinfInv p R),
    IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p S) (AinfInv p S),
    AinfInv.map_algebraMap, Ainf.map_algebraMap]

namespace BdRPlus

def map (f : R →+* S) : BdRPlus p R →+* BdRPlus p S :=
  adicMap _ _ (AinfInv.map p f) (AinfInv.kerTheta_le_comap p f)

variable {p}

theorem eval_map (f : R →+* S) (n : ℕ) (x : BdRPlus p R) :
    eval p S n (map p f x) = Ideal.quotientMap _ (AinfInv.map p f)
      (pow_le_comap_pow (AinfInv.kerTheta_le_comap p f) n) (eval p R n x) :=
  evalₐ_adicMap _ _ _ _ n x

@[simp] theorem map_algebraMap (f : R →+* S) (x : AinfInv p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AinfInv.map p f x) :=
  adicMap_algebraMap _ _ _ _ x

@[simp] theorem map_algebraMap_ainf (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_algebraMap_padic (f : R →+* S) (a : ℚ_[p]) :
    map p f (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap_padic,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_id (x : BdRPlus p R) : map p (RingHom.id R) x = x :=
  adicMap_eq_id _ _ _ AinfInv.map_id x

theorem map_map (f : R →+* S) (g : S →+* U) (x : BdRPlus p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  adicMap_adicMap _ _ _ _ _ _ _ _ _ (AinfInv.map_map f g) x

theorem theta_eq_of_eval_one {x : BdRPlus p R} {a : AinfInv p R}
    (h : eval p R 1 x = Ideal.Quotient.mk _ a) : theta p R x = AinfInv.theta p R a := by
  have h1 := AdicCompletion.factorₐ_evalₐ_one (AinfInv.kerTheta p R) x
  change Ideal.Quotient.factor _ (eval p R 1 x) = _ at h1
  rw [h] at h1
  change RingHom.kerLift _ (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x) = _
  rw [← h1]
  rfl

theorem theta_map (f : R →+* S) (x : BdRPlus p R) :
    theta p S (map p f x) = awayMap p f (theta p R x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R 1 x)
  rw [theta_eq_of_eval_one ha.symm, ← AinfInv.theta_map]
  apply theta_eq_of_eval_one
  rw [eval_map, ← ha, Ideal.quotientMap_mk]

variable (p) in

def mapEquiv (e : R ≃+* S) : BdRPlus p R ≃+* BdRPlus p S :=
  RingEquiv.ofRingHom (map p e.toRingHom) (map p e.symm.toRingHom)
    (by ext x; simp [map_map]) (by ext x; simp [map_map])

@[simp] theorem mapEquiv_apply (e : R ≃+* S) (x : BdRPlus p R) :
    mapEquiv p e x = map p (e : R →+* S) x := rfl

end BdRPlus

namespace BdR

def map (e : R ≃+* S) : BdR p R ≃+* BdR p S :=
  IsFractionRing.ringEquivOfRingEquiv (BdRPlus.mapEquiv p e)

variable {p}

theorem hom_ext {B : Type*} [CommRing B] {f g : BdR p R →+* B}
    (h : ∀ x : BdRPlus p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (BdRPlus p R)) (RingHom.ext h)

@[simp] theorem map_algebraMap (e : R ≃+* S) (x : BdRPlus p R) :
    map p e (algebraMap _ _ x) = algebraMap _ _ (BdRPlus.map p (e : R →+* S) x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

@[simp] theorem map_algebraMap_padic (e : R ≃+* S) (a : ℚ_[p]) :
    map p e (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply _ (BdRPlus p R), map_algebraMap, BdRPlus.map_algebraMap_padic,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_refl (x : BdR p R) : map p (RingEquiv.refl R) x = x :=
  RingHom.congr_fun (hom_ext (f := (map p (RingEquiv.refl R) : _ →+* _)) (g := RingHom.id _)
    (by simp)) x

theorem map_map (e : R ≃+* S) (e' : S ≃+* U) (x : BdR p R) :
    map p e' (map p e x) = map p (e.trans e') x :=
  RingHom.congr_fun (hom_ext (f := (map p e').toRingHom.comp (map p e).toRingHom)
    (g := (map p (e.trans e')).toRingHom) (by simp [BdRPlus.map_map])) x

end BdR

end Reformulated.AutPerF
