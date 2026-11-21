import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsClosedUnitaryOfComplex
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.DivisionPairOfAdelicFormsFaceColumnsData

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField MeasureTheory GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
open scoped ENNReal Matrix ComplexOrder

theorem unitaryOf_smul_eq {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : K →+* K)
    (J : Matrix ι ι K) {r : K} (hr : r ≠ 0) : unitaryOf σ (r • J) = unitaryOf σ J := by
  ext g
  change (g : Matrix ι ι K)ᵀ * (r • J) * (g : Matrix ι ι K).map σ = r • J ↔
    (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K).map σ = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_right_injective _ hr).eq_iff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def scaleSpace (V : HermSpace E N) (n : ℕ) (hn : 0 < n) : HermSpace E N where
  J := (n : E) • V.J
  herm := by
    rw [Matrix.transpose_smul, V.herm]
    ext i j
    simp [Matrix.map_apply, map_natCast]
  nondeg := by
    rw [Matrix.det_smul]
    exact ((Nat.cast_ne_zero.2 hn.ne' : (n : E) ≠ 0).isUnit.pow _).mul V.nondeg

theorem placeJ_scale (V : HermSpace E N) (n : ℕ) (hn : 0 < n) (w : InfinitePlace E) :
    placeJ (scaleSpace V n hn) w = (n : ℂ) • placeJ V w := by
  ext i j
  simp [placeJ, scaleSpace, Matrix.map_apply]

theorem realPoints_scale (V : HermSpace E N) (n : ℕ) (hn : 0 < n) :
    realPoints (scaleSpace V n hn) = realPoints V := by
  unfold realPoints
  congr 1
  funext w
  rw [placeJ_scale]
  exact unitaryOf_smul_eq _ _ (Nat.cast_ne_zero.2 hn.ne')

section Transport

variable (V : HermSpace E N) (n : ℕ) (hn : 0 < n)

def realScale : RealPts V ≃* RealPts (scaleSpace V n hn) where
  toFun g := ⟨g.1, by rw [realPoints_scale]; exact g.2⟩
  invFun g := ⟨g.1, by rw [← realPoints_scale V n hn]; exact g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem realScale_eq_mk (g : RealPts V) :
    realScale V n hn g = ⟨g.1, by rw [realPoints_scale]; exact g.2⟩ := rfl

theorem continuous_realScale : Continuous (realScale V n hn) :=
  continuous_subtype_val.subtype_mk _

theorem continuous_realScale_symm : Continuous (realScale V n hn).symm :=
  continuous_subtype_val.subtype_mk _

def realScaleMeas : RealPts V ≃ᵐ RealPts (scaleSpace V n hn) :=
  (Homeomorph.mk (realScale V n hn).toEquiv (continuous_realScale V n hn)
    (continuous_realScale_symm V n hn)).toMeasurableEquiv

theorem realScaleMeas_apply (g : RealPts V) : realScaleMeas V n hn g = realScale V n hn g := rfl

end Transport

end GroundTheory.Heights₂.Heights.NineStatements
