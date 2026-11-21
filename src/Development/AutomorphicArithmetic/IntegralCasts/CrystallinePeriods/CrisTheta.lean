import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]

namespace AinfInv

theorem isUnit_factorial (n : ℕ) : IsUnit (n ! : AinfInv p R) :=
  IsUnit.natCast_factorial_of_algebra ℚ n

@[simp] theorem gamma_zero (x : AinfInv p R) : gamma 0 x = 1 := by simp [gamma]

@[simp] theorem gamma_one (x : AinfInv p R) : gamma 1 x = x := by simp [gamma]

end AinfInv

variable [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

theorem AinfInv.theta_gamma {n : ℕ} (hn : n ≠ 0) {x : AinfInv p R} (hx : AinfInv.theta p R x = 0) :
    AinfInv.theta p R (AinfInv.gamma n x) = 0 := by
  have h := congrArg (AinfInv.theta p R) (AinfInv.factorial_mul_gamma n x)
  rw [map_mul, map_pow, hx, zero_pow hn] at h
  exact (((AinfInv.isUnit_factorial n).map (AinfInv.theta p R)).mul_right_eq_zero).1 h

namespace AcrisZero

variable (p R) in

def pdIdeal : Ideal (AcrisZero p R) :=
  span {y | ∃ (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0), n ≠ 0 ∧ y = gamma n x hx}

theorem gamma_mem_pdIdeal {n : ℕ} (hn : n ≠ 0) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    gamma n x hx ∈ pdIdeal p R := subset_span ⟨n, x, hx, hn, rfl⟩

theorem algebraMap_mem_pdIdeal (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    algebraMap _ _ x ∈ pdIdeal p R := by
  have : algebraMap _ _ x = gamma 1 x hx := Subtype.ext (AinfInv.gamma_one _).symm
  rw [this]
  exact gamma_mem_pdIdeal one_ne_zero x hx

theorem exists_sub_mem_pdIdeal (y : AcrisZero p R) :
    ∃ a : Ainf p R, y - algebraMap _ _ a ∈ pdIdeal p R := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨1, ?_⟩
      convert (pdIdeal p R).zero_mem
      rw [sub_eq_zero, map_one]
      exact Subtype.ext (AinfInv.gamma_zero _)
    · exact ⟨0, by rw [map_zero, sub_zero]; exact gamma_mem_pdIdeal hn x hx⟩
  | algebraMap r =>
    refine ⟨r, ?_⟩
    convert (pdIdeal p R).zero_mem
    rw [sub_eq_zero]
    rfl
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    change (⟨x, hx'⟩ + ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_add]; ring
  | mul x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    convert add_mem (Ideal.mul_mem_right ⟨y, hy'⟩ _ ha)
      (Ideal.mul_mem_left _ (algebraMap _ _ a) hb) using 1
    change (⟨x, hx'⟩ * ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_mul]; ring

theorem theta_eq_zero_of_mem_pdIdeal {y : AcrisZero p R} (hy : y ∈ pdIdeal p R) :
    AinfInv.theta p R y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, hn, rfl⟩ := hy
    exact AinfInv.theta_gamma hn (by rw [AinfInv.theta_algebraMap, hx, map_zero])
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [AddMemClass.coe_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, hx, mul_zero]

theorem exists_theta_eq (y : AcrisZero p R) :
    ∃ r : R, algebraMap R (Localization.Away (p : R)) r = AinfInv.theta p R y := by
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h := theta_eq_zero_of_mem_pdIdeal ha
  rw [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero, Subalgebra.coe_algebraMap,
    AinfInv.theta_algebraMap] at h
  exact ⟨_, h.symm⟩

end AcrisZero

variable [IsDomain R] [CharZero R] [IsDomain S] [CharZero S]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective (M := Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

namespace AcrisZero

variable (p R) in

def theta : AcrisZero p R →+* R where
  toFun y := (exists_theta_eq y).choose
  map_one' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_mul' x y := algebraMap_away_injective (p := p) (by
    rw [map_mul, (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)
  map_zero' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_add' x y := algebraMap_away_injective (p := p) (by
    rw [map_add, (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)

theorem algebraMap_theta (y : AcrisZero p R) :
    algebraMap R (Localization.Away (p : R)) (theta p R y) = AinfInv.theta p R y :=
  (exists_theta_eq y).choose_spec

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x :=
  algebraMap_away_injective (p := p) (by
    rw [algebraMap_theta, Subalgebra.coe_algebraMap, AinfInv.theta_algebraMap])

theorem theta_eq_zero_iff (y : AcrisZero p R) : theta p R y = 0 ↔ y ∈ pdIdeal p R := by
  have key : ∀ y ∈ pdIdeal p R, theta p R y = 0 := fun y hy =>
    algebraMap_away_injective (p := p) (by
      rw [algebraMap_theta, theta_eq_zero_of_mem_pdIdeal hy, map_zero])
  refine ⟨fun h => ?_, key y⟩
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h1 := key _ ha
  rw [map_sub, h, theta_algebraMap, zero_sub, neg_eq_zero] at h1
  simpa using add_mem ha (algebraMap_mem_pdIdeal a h1)

@[simp] theorem theta_gamma {n : ℕ} (hn : n ≠ 0) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    theta p R (gamma n x hx) = 0 :=
  (theta_eq_zero_iff _).2 (gamma_mem_pdIdeal hn x hx)

end AcrisZero

namespace Acris

variable (p R) in

def theta : Acris p R →+* R :=
  ((AdicCompletion.ofAlgEquiv (span {(p : R)})).symm : _ →+* R).comp
    (adicMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _))

@[simp] theorem theta_algebraMap_zero (a : AcrisZero p R) :
    theta p R (algebraMap _ _ a) = AcrisZero.theta p R a := by
  have h := adicMap_algebraMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _) a
  refine (congrArg (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm h).trans ?_
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), theta_algebraMap_zero,
    AcrisZero.theta_algebraMap]

@[simp] theorem theta_log (u : Ainf p R) (hu : Ainf.theta p R u = 1) : theta p R (log u hu) = 0 := by
  refine IsHausdorff.haus (I := span {(p : R)}) inferInstance _ fun n => ?_
  obtain ⟨y, hy⟩ := (eval_eq_zero_iff n (log u hu - algebraMap _ _ (logPartial (p ^ n) u hu))).1
    (by rw [map_sub, eval_log u hu le_rfl, eval_algebraMap, sub_self])
  have h0 : AcrisZero.theta p R (logPartial (p ^ n) u hu) = 0 := by
    rw [logPartial, map_sum]
    exact Finset.sum_eq_zero fun k _ => by
      rw [map_mul, AcrisZero.theta_gamma (Nat.succ_ne_zero k), mul_zero]
  have h := congrArg (theta p R) hy
  rw [map_sub, theta_algebraMap_zero, h0, sub_zero, map_mul, map_pow, map_natCast] at h
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨_, h⟩

@[simp] theorem theta_logTeich (η : tateModule p R) : theta p R (logTeich η) = 0 := theta_log _ _

end Acris

namespace BcrisPlus

variable (p R) in

def theta : BcrisPlus p R →+* Localization.Away (p : R) :=
  lift ((algebraMap R _).comp (Acris.theta p R))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : R)) (p : R))

@[simp] theorem theta_algebraMap (x : Acris p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Acris.theta p R x) := lift_algebraMap _ _ x

end BcrisPlus

end Reformulated.AutPerF
