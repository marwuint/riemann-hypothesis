import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqMulSecOfEqZpowSec

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter DirectSum
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory

namespace Twist

variable {X : Scheme.{0}} {F : X.Modules} {L : LB X} {m n : ℤ}

def RingPiece (L : LB X) (n : ℤ) : Type := LB.Sec (lbZPow L n)

instance (n : ℤ) : AddCommGroup (RingPiece L n) :=
  inferInstanceAs (AddCommGroup (LB.Sec (lbZPow L n)))

theorem ringPiece_mk_ext {m' : ℤ} {σ : LB.Sec (lbZPow L m)} {τ : LB.Sec (lbZPow L m')} (h : m = m')
    (e : ∀ i, zfun σ i = zfun τ i) :
    GradedMonoid.mk (A := RingPiece L) m σ = GradedMonoid.mk (A := RingPiece L) m' τ := by
  subst h
  rw [zglobal_ext e]

theorem ringPiece_mk_assoc {p q r : ℤ} (a : LB.Sec (lbZPow L p)) (b : LB.Sec (lbZPow L q))
    (c : LB.Sec (lbZPow L r)) :
    GradedMonoid.mk (A := RingPiece L) (p + q + r) (zmul (zmul a b) c) =
      GradedMonoid.mk (A := RingPiece L) (p + (q + r)) (zmul a (zmul b c)) :=
  ringPiece_mk_ext (add_assoc _ _ _) fun i => by simp only [zfun_zmul, mul_assoc]

instance : GCommRing (RingPiece L) :=
  letI : GradedMonoid.GMul (RingPiece L) := ⟨fun σ τ => zmul σ τ⟩
  letI : GradedMonoid.GOne (RingPiece L) := ⟨zone L⟩
  { mul_zero := fun a => zglobal_ext fun i =>
      (zfun_zmul a 0 i).trans (by rw [zfun_zero, mul_zero]; exact (zfun_zero i).symm)
    zero_mul := fun a => zglobal_ext fun i =>
      (zfun_zmul 0 a i).trans (by rw [zfun_zero, zero_mul]; exact (zfun_zero i).symm)
    mul_add := fun {p q} (a : LB.Sec (lbZPow L p)) (b c : LB.Sec (lbZPow L q)) =>
      zglobal_ext (σ := zmul a (b + c)) (τ := zmul a b + zmul a c) fun i => by
        simp only [zfun_zmul, zfun_add, mul_add]
    add_mul := fun {p q} (a b : LB.Sec (lbZPow L p)) (c : LB.Sec (lbZPow L q)) =>
      zglobal_ext (σ := zmul (a + b) c) (τ := zmul a c + zmul b c) fun i => by
        simp only [zfun_zmul, zfun_add, add_mul]
    one_mul := fun ⟨p, (a : LB.Sec (lbZPow L p))⟩ =>
      ringPiece_mk_ext (σ := zmul (zone L) a) (τ := a) (zero_add _) fun i =>
        (zfun_zmul _ _ i).trans (by rw [zfun_zone, one_mul])
    mul_one := fun ⟨p, (a : LB.Sec (lbZPow L p))⟩ =>
      ringPiece_mk_ext (σ := zmul a (zone L)) (τ := a) (add_zero _) fun i =>
        (zfun_zmul _ _ i).trans (by rw [zfun_zone, mul_one])
    mul_assoc := fun a b c => ringPiece_mk_assoc a.2 b.2 c.2
    mul_comm := fun a b => ringPiece_mk_ext (σ := zmul a.2 b.2) (τ := zmul b.2 a.2) (add_comm _ _)
      fun i => (zfun_zmul _ _ i).trans ((mul_comm _ _).trans (zfun_zmul _ _ i).symm)
    natCast := fun k => k • (GradedMonoid.GOne.one : RingPiece L 0)
    natCast_zero := zero_nsmul _
    natCast_succ := fun k => succ_nsmul _ k
    intCast := fun k => k • (GradedMonoid.GOne.one : RingPiece L 0)
    intCast_ofNat := fun k => natCast_zsmul _ k
    intCast_negSucc_ofNat := fun k => negSucc_zsmul _ k }

abbrev SecRing (L : LB X) : Type := ⨁ n, RingPiece L n

def SecRing.of (m : ℤ) : LB.Sec (lbZPow L m) →+ SecRing L := DirectSum.of (RingPiece L) m

theorem SecRing.one_def : (1 : SecRing L) = SecRing.of 0 (zone L) := rfl

def ModulePiece (F : X.Modules) (L : LB X) (V : X.Opens) (n : ℤ) : Type := Γ(twistZ F L n, V)

variable {U V W : X.Opens}

instance (n : ℤ) : AddCommGroup (ModulePiece F L V n) :=
  inferInstanceAs (AddCommGroup Γ(twistZ F L n, V))

theorem modulePiece_mk_ext {n' : ℤ} {a : Γ(twistZ F L n, V)} {b : Γ(twistZ F L n', V)} (h : n = n')
    (e : ∀ i, zcoord a i = zcoord b i) :
    GradedMonoid.mk (A := ModulePiece F L V) n a = GradedMonoid.mk (A := ModulePiece F L V) n' b := by
  subst h
  rw [zsec_ext e]

theorem modulePiece_mk_one (a : Γ(twistZ F L n, V)) :
    GradedMonoid.mk (A := ModulePiece F L V) (0 + n)
      ((mulSecOfEq F (zone L) (add_comm _ _)).app V a) =
      GradedMonoid.mk (A := ModulePiece F L V) n a :=
  modulePiece_mk_ext (zero_add _) fun i => by
    rw [zcoord_mulSecOfEq_app, zfun_zone, map_one, one_smul]

theorem modulePiece_mk_mul {p q : ℤ} (σ : LB.Sec (lbZPow L p)) (τ : LB.Sec (lbZPow L q))
    (a : Γ(twistZ F L n, V)) :
    GradedMonoid.mk (A := ModulePiece F L V) (p + q + n)
      ((mulSecOfEq F (zmul σ τ) (add_comm _ _)).app V a) =
      GradedMonoid.mk (A := ModulePiece F L V) (p + (q + n))
        ((mulSecOfEq F σ (add_comm _ _)).app V ((mulSecOfEq F τ (add_comm n q)).app V a)) :=
  modulePiece_mk_ext (add_assoc _ _ _) fun i => by
    simp only [zcoord_mulSecOfEq_app, zfun_zmul, map_mul, mul_smul]

instance : Gmodule (RingPiece L) (ModulePiece F L V) :=
  letI : GradedMonoid.GSMul (RingPiece L) (ModulePiece F L V) :=
    ⟨fun {p q} σ a => (mulSecOfEq F (L := L) σ (add_comm q p)).app V a⟩
  { one_smul := fun a => modulePiece_mk_one a.2
    mul_smul := fun σ τ a => modulePiece_mk_mul σ.2 τ.2 a.2
    smul_add := fun σ a b => map_add ((mulSecOfEq F (L := L) σ (add_comm _ _)).app V).hom a b
    smul_zero := fun σ => map_zero ((mulSecOfEq F (L := L) σ (add_comm _ _)).app V).hom
    add_smul := fun {p q} (σ τ : LB.Sec (lbZPow L p)) a => by
      change (mulSecOfEq F (σ + τ) (add_comm q p)).app V a = _
      rw [mulSecOfEq_add]
      rfl
    zero_smul := fun {p q} a => by
      change (mulSecOfEq F (0 : LB.Sec (lbZPow L p)) (add_comm q p)).app V a = _
      rw [mulSecOfEq_zero]
      rfl }

abbrev SecModule (F : X.Modules) (L : LB X) (V : X.Opens) : Type := ⨁ n, ModulePiece F L V n

namespace SecModule

def of (n : ℤ) : Γ(twistZ F L n, V) →+ SecModule F L V := DirectSum.of (ModulePiece F L V) n

theorem of_smul_of (σ : LB.Sec (lbZPow L m)) (a : Γ(twistZ F L n, V)) {d : ℤ} (h : n + m = d) :
    SecRing.of m σ • of n a = of d ((mulSecOfEq F σ h).app V a) :=
  (Gmodule.of_smul_of (RingPiece L) (ModulePiece F L V) σ a).trans
    (of_eq_of_gradedMonoid_eq (modulePiece_mk_ext
      (a := (mulSecOfEq F σ (add_comm _ _)).app V a) ((add_comm _ _).trans h) fun i => by
        simp only [zcoord_mulSecOfEq_app]))

@[elab_as_elim]
theorem induction_on {P : SecModule F L V → Prop} (y : SecModule F L V) (zero : P 0)
    (hof : ∀ n a, P (of n a)) (add : ∀ y z, P y → P z → P (y + z)) : P y :=
  DirectSum.induction_on y zero hof add

variable (F L) in

def resAdd (h : W ≤ V) : SecModule F L V →+ SecModule F L W :=
  DirectSum.map (α := ModulePiece F L V) (β := ModulePiece F L W) fun n => resM (twistZ F L n) h

theorem resAdd_of (h : W ≤ V) (a : Γ(twistZ F L n, V)) :
    resAdd F L h (of n a) = of n (resM _ h a) :=
  DirectSum.map_of (α := ModulePiece F L V) (β := ModulePiece F L W) _ n a

variable (F L) in

def res (h : W ≤ V) : SecModule F L V →ₗ[SecRing L] SecModule F L W where
  __ := resAdd F L h
  map_smul' r y := by
    change resAdd F L h (r • y) = r • resAdd F L h y
    induction r using DirectSum.induction_on with
    | zero => rw [zero_smul, zero_smul, map_zero]
    | add r s hr hs => rw [add_smul, add_smul, map_add, hr, hs]
    | of p σ =>
      induction y using induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add y z hy hz => rw [smul_add, map_add, map_add, smul_add, hy, hz]
      | hof q a =>
        change resAdd F L h (SecRing.of p σ • _) = SecRing.of p σ • _
        rw [resAdd_of, of_smul_of σ a rfl, of_smul_of σ _ rfl, resAdd_of, app_resM]

@[simp] theorem res_of (h : W ≤ V) (a : Γ(twistZ F L n, V)) :
    res F L h (of n a) = of n (resM _ h a) := resAdd_of h a

theorem res_apply (h : W ≤ V) (y : SecModule F L V) (n : ℤ) :
    (res F L h y n : Γ(twistZ F L n, W)) = resM (twistZ F L n) h (y n) := rfl

end SecModule

end Twist

end GlobalTheory
