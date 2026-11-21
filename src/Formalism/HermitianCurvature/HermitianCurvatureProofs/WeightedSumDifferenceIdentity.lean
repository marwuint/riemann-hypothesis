import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingConstantEqNablaStar

namespace Formalism.FourierDecayAlt.P.Mx7

section PartT

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem kap_eq (P : Par) (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := rfl

theorem kap_comm_diagonal (P : Par) (f : Ty P → ℂ) (d : Ty P → Pr P.r) :
    Commute (kap P f) (Matrix.diagonal d) := by
  show kap P f * Matrix.diagonal d = Matrix.diagonal d * kap P f
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

theorem kap_comm_sc (P : Par) (f : Ty P → ℂ) (w : Pr P.r) : Commute (kap P f) (sc P w) := by
  have : sc P w = Matrix.diagonal fun _ => w := by simp [sc, Matrix.scalar_apply]
  rw [this]; exact kap_comm_diagonal P f _

theorem kap_comm_nab (P : Par) (f : Ty P → ℂ) : Commute (kap P f) (nabA P) := kap_comm_diagonal P f _

theorem kap_comm_nabs (P : Par) (f : Ty P → ℂ) : Commute (kap P f) (nabsA P) := kap_comm_diagonal P f _

end PartT

section PartA

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial

section Poly

variable {B : Type} [Ring B] [Algebra ℂ B]

noncomputable def ev (Y : ℂ) : B[X] →+* B :=
  eval₂RingHom' (RingHom.id B) (algebraMap ℂ B Y) (fun a => (Algebra.commutes Y a).symm)

theorem ev_apply (Y : ℂ) (p : B[X]) : ev Y p = eval₂ (RingHom.id B) (algebraMap ℂ B Y) p := rfl

theorem ev_C (Y : ℂ) (a : B) : ev Y (C a) = a := by rw [ev_apply, eval₂_C]; rfl

theorem ev_X (Y : ℂ) : ev Y (X : B[X]) = algebraMap ℂ B Y := by rw [ev_apply, eval₂_X]

theorem ev_monomial (Y : ℂ) (n : ℕ) (a : B) : ev Y (monomial n a) = a * algebraMap ℂ B Y ^ n := by
  rw [ev_apply, eval₂_monomial]; rfl

theorem ev_eq_sum (Y : ℂ) (p : B[X]) : ev Y p = ∑ i ∈ p.support, Y ^ i • p.coeff i := by
  rw [ev_apply, eval₂_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]

theorem ev_comp (Y c : ℂ) (p : B[X]) : ev Y (p.comp (X + C (algebraMap ℂ B c))) = ev (Y + c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, hp, hq]
  | monomial n a => rw [monomial_comp, map_mul, map_pow, map_add, ev_C, ev_X, ev_C, ev_monomial, map_add]

def IsPoly (F : ℂ → B) : Prop := ∃ p : B[X], ∀ Y, F Y = ev Y p

theorem IsPoly.congr {F G : ℂ → B} (hF : IsPoly F) (h : ∀ Y, G Y = F Y) : IsPoly G := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p, fun Y => by rw [h, hp]⟩

theorem IsPoly.add {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y + G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun Y => by show F Y + G Y = _; rw [map_add, hp, hq]⟩

theorem IsPoly.sub {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y - G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun Y => by show F Y - G Y = _; rw [map_sub, hp, hq]⟩

theorem IsPoly.neg {F : ℂ → B} (hF : IsPoly F) : IsPoly (fun Y => -F Y) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨-p, fun Y => by show -F Y = _; rw [map_neg, hp]⟩

theorem IsPoly.mul {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y * G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p * q, fun Y => by show F Y * G Y = _; rw [map_mul, hp, hq]⟩

theorem IsPoly.shift {F : ℂ → B} (hF : IsPoly F) (c : ℂ) : IsPoly (fun Y => F (Y + c)) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p.comp (X + C (algebraMap ℂ B c)), fun Y => by show F (Y + c) = _; rw [ev_comp, hp]⟩

theorem IsPoly.eq_zero {F : ℂ → B} (hF : IsPoly F) {S : Set ℂ} (hS : S.Finite) (h : ∀ Y, Y ∉ S → F Y = 0)
    (Y : ℂ) : F Y = 0 := by
  obtain ⟨p, hp⟩ := hF
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hev : ∀ Z, φ (F Z) = (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]).eval Z := by
    intro Z
    rw [hp, ev_eq_sum, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
  have h0 : (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]) = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine hS.infinite_compl.mono ?_
    intro Z hZ
    show eval Z _ = 0
    rw [← hev, h Z hZ, map_zero]
  rw [hev, h0, eval_zero]

theorem IsPoly.ext {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) {S : Set ℂ} (hS : S.Finite)
    (h : ∀ Y, Y ∉ S → F Y = G Y) (Y : ℂ) : F Y = G Y :=
  sub_eq_zero.1 ((hF.sub hG).eq_zero hS (fun Z hZ => sub_eq_zero.2 (h Z hZ)) Y)

end Poly

end PartA

section PartB

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem star_kap (P : Par) (f : Ty P → ℂ) : star (kap P f) = kap P (fun π => star (f π)) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun π => ?_)
  exact (algebraMap_star_comm (f π)).symm

noncomputable def Ul (P : Par) (Y : ℂ) : A P :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j

noncomputable def Um (P : Par) (Y : ℂ) : A P :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P j)

theorem lA_eq (P : Par) (Y : ℂ) : lA P Y = l0A P Y + ggiA P * Ul P Y := rfl
theorem mA_eq (P : Par) (Y : ℂ) : mA P Y = m0A P Y + ggiA P * Um P Y := rfl

end PartB

end Formalism.FourierDecayAlt.P.Mx7

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
