import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

section Poly

variable {A : Type u} [CommRing A]

theorem eq_C_of_derivative_eq_zero (h : ∀ n : ℕ, IsUnit ((n : A) + 1)) {f : Polynomial A}
    (hf : Polynomial.derivative f = 0) : f = Polynomial.C (f.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp
  · have h1 := Polynomial.coeff_derivative f n
    rw [hf, Polynomial.coeff_zero] at h1
    rw [Polynomial.coeff_C_succ]
    exact (h n).mul_left_eq_zero.1 h1.symm

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

open tateModule

theorem Acris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := exists_padicPow_eq η h
  obtain ⟨b, hb⟩ := h
  refine ⟨Acris.logTeich η' - algebraMap ℤ_[p] (Acris p R) b * Acris.logTeich η, ?_⟩
  have ha : algebraMap ℤ_[p] (Acris p R) a =
      (a.appr k : Acris p R) + (p : Acris p R) ^ k * algebraMap ℤ_[p] (Acris p R) b := by
    conv_lhs => rw [← sub_add_cancel a (a.appr k), hb]
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast, add_comm]
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, ha, Nat.cast_pow]
  ring

theorem Bcris.algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (Bcris p R) a =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] (Acris p R) a) :=
  congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) (BcrisPlus.algebraMap_padicInt a)

theorem IsPrimitive.isLocalization_away [IsDomain R] {ε : tateModule p R} (hε : IsPrimitive ε) :
    IsLocalization.Away (algebraMap (Acris p R) (BcrisPlus p R) (Acris.logTeich ε))
      (Bcris p R) := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := Bcris p R) _ (BcrisPlus.periods p R)
    ?_ ?_).2 inferInstance
  · exact Submonoid.powers_le.2 (Submonoid.subset_closure ⟨ε, hε, rfl⟩)
  · intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨ε', hε', rfl⟩ := hx
      obtain ⟨a, ha⟩ := hε'.exists_unit hε
      refine ⟨_, Submonoid.mem_powers _, ?_⟩
      rw [ha, Acris.logTeich_padicPow, map_mul]
      exact dvd_mul_left _ _
    | one => exact ⟨1, one_mem _, dvd_rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      exact ⟨a * b, mul_mem ha hb, mul_dvd_mul hxa hyb⟩

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)] [CharZero R]

variable (p R)

def Acris.t : Acris p R := Acris.logTeich (eps p R)

def BcrisPlus.t : BcrisPlus p R := algebraMap (Acris p R) _ (Acris.t p R)

def Bcris.t : Bcris p R := algebraMap (Acris p R) _ (Acris.t p R)

instance Bcris.isLocalization_away_alt : IsLocalization.Away (BcrisPlus.t p R) (Bcris p R) :=
  (isPrimitive_eps p R).isLocalization_away

variable {p R}

end Good

namespace Bst

open Polynomial

variable [IsDomain R] [CharZero R] [ValuationRing R]

def toPolynomial (ϖ : PFlat p R) : Bst p R →ₐ[Bcris p R] (Bcris p R)[X] :=
  { lift (C : Bcris p R →+* (Bcris p R)[X]) (fun ϖ' => C (Bcris.logTeich (ϖ'.div ϖ)) + X)
      (fun η ϖ' => by rw [PFlat.twist_div_eq, Bcris.logTeich_mul, map_add, add_assoc]) with
    commutes' := fun x => lift_algebraMap _ _ _ x }

theorem toPolynomial_logFlat (ϖ ϖ' : PFlat p R) :
    toPolynomial ϖ (logFlat ϖ') = C (Bcris.logTeich (ϖ'.div ϖ)) + X :=
  lift_logFlat (C : Bcris p R →+* (Bcris p R)[X]) (fun ϖ' => C (Bcris.logTeich (ϖ'.div ϖ)) + X)
    (fun η ϖ' => by rw [PFlat.twist_div_eq, Bcris.logTeich_mul, map_add, add_assoc]) ϖ'

def polynomialEquiv (ϖ : PFlat p R) : (Bcris p R)[X] ≃ₐ[Bcris p R] Bst p R :=
  AlgEquiv.ofAlgHom (aeval (logFlat ϖ)) (toPolynomial ϖ)
    (AlgHom.coe_ringHom_injective (hom_ext (fun x => by simp) (fun ϖ' => by
      change aeval (logFlat ϖ) (toPolynomial ϖ (logFlat ϖ')) = logFlat ϖ'
      rw [toPolynomial_logFlat, map_add, aeval_C, aeval_X, ← logFlat_twist, PFlat.twist_div])))
    (Polynomial.algHom_ext (by simp [toPolynomial_logFlat]))

@[simp] theorem polynomialEquiv_X (ϖ : PFlat p R) : polynomialEquiv ϖ X = logFlat ϖ :=
  aeval_X _

@[simp] theorem polynomialEquiv_C (ϖ : PFlat p R) (x : Bcris p R) :
    polynomialEquiv ϖ (C x) = algebraMap _ _ x := aeval_C _ _

variable [IsAlgClosed (FractionRing R)]

variable (p R) in

def u : Bst p R := logFlat (pflat p R)

@[simp] theorem monodromy_u : monodromy p R (u p R) = -1 := monodromy_logFlat _

end Bst

end Reformulated.AutPerF
