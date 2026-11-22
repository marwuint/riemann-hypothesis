import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

def dualLattice {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    Submodule ℤ (Fin i → K) where
  carrier := {φ | ∀ x ∈ F.lattice, φ ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range}
  add_mem' {φ ψ} hφ hψ x hx := by
    rw [add_dotProduct]
    exact add_mem (hφ x hx) (hψ x hx)
  zero_mem' x _ := by
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' c φ hφ x hx := by
    rw [smul_dotProduct]
    exact zsmul_mem (hφ x hx) c

abbrev dualBlocks (T : Type) : Unit → Type := fun _ => T

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def dualLatticeCoord (b : Module.Basis T ℤ (dualLattice F)) : (Σ _ : Unit, T) → ProjField K i :=
  fun p => algebraMap (MvPolynomial (Fin i) K) (ProjField K i)
    (∑ j, C ((b p.2 : Fin i → K) j) * X j)

def dualIdeal (b : Module.Basis T ℤ (dualLattice F)) : Ideal (MRing (dualBlocks T)) :=
  mCoordIdeal (dualLatticeCoord b)

def dualEmbMatrix (b : Module.Basis T ℤ (dualLattice F)) : Matrix T ((K →+* ℂ) × Fin i) ℂ :=
  fun t p => p.1 ((b t : Fin i → K) p.2)

def dualRecover (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    (T → ℂ) ≃ₗ[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
  (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).symm

def dualNormSq (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (fun j => dualRecover b hb z (σ, j)) ⬝ᵥ
    (F.metric σ *ᵥ fun j => dualRecover b hb z (σ, j))).re

theorem dualNormSq_term_nonneg (σ : K →+* ℂ) (w : Fin i → ℂ) :
    0 ≤ (star w ⬝ᵥ (F.metric σ *ᵥ w)).re := by
  by_cases hw : w = 0
  · simp [hw]
  · exact ((Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hw)).1).le

def dualLine (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : HermLine (dualBlocks T) where
  a := fun _ => 1
  h z := Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  pos z hz := by
    apply Real.sqrt_pos.mpr
    obtain ⟨t, ht⟩ := hz ()
    have hne : dualRecover b hb (fun t => z ⟨(), t⟩) ≠ 0 := by
      intro h0
      apply ht
      have := congrArg (fun v => v t) ((dualRecover b hb).map_eq_zero_iff.mp h0)
      simpa using this
    obtain ⟨⟨σ, j⟩, hσj⟩ := Function.ne_iff.mp hne
    have hσ : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)) ≠ 0 := by
      intro h0
      exact hσj (congrFun h0 j)
    have hpos := (Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hσ)).1
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun σ =>
      (star (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)) ⬝ᵥ
        (F.metric σ *ᵥ fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j))).re)
      (fun σ _ => dualNormSq_term_nonneg σ _) (Finset.mem_univ σ))
  smul c z hc := by
    have hz : (fun t => (fun p : Σ _ : Unit, T => c p.1 * z p) ⟨(), t⟩) =
        c () • fun t => z ⟨(), t⟩ := by
      funext t; rfl
    simp only [hz, dualNormSq, map_smul, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    have : ∀ σ : K →+* ℂ,
        (star (fun j => (c () • dualRecover b hb fun t => z ⟨(), t⟩) (σ, j)) ⬝ᵥ
          (F.metric σ *ᵥ fun j => (c () • dualRecover b hb fun t => z ⟨(), t⟩) (σ, j))).re =
        ‖c ()‖ ^ 2 * (star (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)) ⬝ᵥ
          (F.metric σ *ᵥ fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j))).re := by
      intro σ
      have hs : (fun j => (c () • dualRecover b hb fun t => z ⟨(), t⟩) (σ, j)) =
          c () • fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by
        funext j; rfl
      rw [hs, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
    simp only [this, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

def DualLatticeBasisExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i),
    ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T), Nonempty (Module.Basis T ℤ (dualLattice F))

def DualEmbBijective.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))

def DualArithVar.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)), 1 ≤ i → IsArithVar (dualIdeal b) i

def DualLineSemipositive.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    IsSemipositiveRel ⊥ (dualIdeal b) (dualLine F b hb)

def DualLineConj.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    IsConjInvariantH (dualLine F b hb)

def DualPointLineDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 →
      dualIdeal b ≤ W → 0 < degC W ∧
        ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
          v ≠ 0 ∧ F.lineDegree K' v = -II Unit (dualBlocks T) W 1 ![dualLine F b hb] / degC W

def DualTopBound.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type)
    [Fintype T] [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) (dualLine F b hb) (i - 1)

def DualGeomDegPos.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    0 < geomDeg (dualIdeal b) (dualLine F b hb) (i - 1)

end

end GroundTheory.Heights₂.Heights
