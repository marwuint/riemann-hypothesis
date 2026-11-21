import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep

set_option autoImplicit false
noncomputable section
open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix
namespace GlobalTheory.GoodMetric.PolyRep
variable {ι : Type} {m : ι → ℕ}

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in

theorem _root_.GlobalTheory.GoodMetric.PolyRep.lie_proj_model [Fintype ι] (τ : ι) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) : (_root_.GlobalTheory.GoodMetric.PolyRep.proj m τ).lie A = A τ := by
  classical
  ext i j
  simp [_root_.GlobalTheory.GoodMetric.PolyRep.lie, _root_.GlobalTheory.GoodMetric.PolyRep.proj, pderiv_X, Pi.single_apply]
  rfl

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in
private lemma aeval_dualNumber_inl_add_inr {σ : Type} [Fintype σ] {R : Type} [CommRing R]
    (x y : σ → R) (p : MvPolynomial σ ℤ) :
    aeval (fun v => (TrivSqZeroExt.inl (x v) + TrivSqZeroExt.inr (y v) : DualNumber R)) p
      = TrivSqZeroExt.inl (aeval x p) + TrivSqZeroExt.inr (∑ v, aeval x (pderiv v p) * y v) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => ext <;> simp
  | add p q hp hq =>
    rw [map_add, hp, hq]
    ext <;> simp [Finset.sum_add_distrib, add_mul]
  | mul_X p v hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
        Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
        Finset.sum_add_distrib]
      simp [Pi.single_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, add_comm]

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in

theorem _root_.GlobalTheory.GoodMetric.PolyRep.ev_dual_model [Fintype ι] (ρ : _root_.GlobalTheory.GoodMetric.PolyRep m) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) (i j : Fin ρ.M) :
    ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : _root_.GlobalTheory.FlagBundle.Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b)) i j
      = TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) i j) + TrivSqZeroExt.inr (ρ.lie A i j) := by
  have h1 := congrFun (congrFun (ρ.one R) i) j
  simp only [_root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply] at h1
  simp only [_root_.GlobalTheory.GoodMetric.PolyRep.ev, _root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply, Matrix.of_apply,
    _root_.GlobalTheory.GoodMetric.PolyRep.lie]
  refine (aeval_dualNumber_inl_add_inr (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => (1 : _root_.GlobalTheory.FlagBundle.Mat m R) v.1 v.2.1 v.2.2)
    (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => A v.1 v.2.1 v.2.2) _).trans ?_
  rw [h1]

end GlobalTheory.GoodMetric.PolyRep
end
