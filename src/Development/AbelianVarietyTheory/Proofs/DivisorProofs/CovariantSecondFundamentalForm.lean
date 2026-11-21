import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem mContDiffAt_orthLift {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthLift (H x)) z := by
  have hc : MContDiffAt k (fun x => orthCoeff (H x)) z :=
    (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
  rintro (a | a) b
  exacts [hc.neg a b, contDiffAt_const]

theorem trace_eq_blocks (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    T.trace = (blockSS K T).trace + (blockQQ K T).trace := by
  rw [blockSS, blockQQ, trace_mul_cycle, trace_mul_cycle (quotMap m l), ← trace_add,
    ← Matrix.add_mul, incl_mul_orthProj_add, Matrix.one_mul]

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem isUnit_sub (h : IsPosFrame U H) (z : V) (hz : z ∈ U) : IsUnit (subGram (H z)).det :=
  h.sub.isHermFrame.isUnit z hz

section Smooth

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz

omit hs in

theorem smooth_secondForm (ξ : V) : MContDiffAt ∞ (fun x => secondForm H x ξ) z :=
  ((mContDiffAt_const _).mul ((h.mContDiffAt hz).conn (h.isUnit z hz) le_rfl ξ)).mul
    (mContDiffAt_const _)

theorem smooth_secondFormAdj (ξ : V) : MContDiffAt ∞ (fun x => secondFormAdj H x ξ) z :=
  ((((h.sub hs).mContDiffAt hz).transpose.inv (by rw [det_transpose]; exact hs z hz)).mul
    (smooth_secondForm h hz ξ).conjTranspose).mul ((h.quot hs).mContDiffAt hz).transpose

theorem smooth_extForm (ξ : V) : MContDiffAt ∞ (fun x => extForm H x ξ) z := by
  have hl := mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)
  simp only [extForm_eq_neg_mdbar]
  have hc : MContDiffAt ∞ (fun x => orthCoeff (H x)) z := fun a b => by
    simpa [orthLift] using hl.neg (.inl a) b
  exact (hc.mdbar le_rfl ξ).neg

theorem smooth_extFormAdj (ξ : V) : MContDiffAt ∞ (fun x => extFormAdj H x ξ) z :=
  ((((h.quot hs).mContDiffAt hz).transpose.inv
    (by rw [det_transpose]; exact (h.quot hs).isUnit z hz)).mul
    (smooth_extForm h hs hz ξ).conjTranspose).mul ((h.sub hs).mContDiffAt hz).transpose

end Smooth

end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
