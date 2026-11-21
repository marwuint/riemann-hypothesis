import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.ProvRowSide

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def stdHLat (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := L

theorem stdHLat_frames (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) :
    IsUnit ((stdHLat K n L).X v).det := by
  show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
  simp

variable {K}

def coordMap (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W) :
    (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

set_option linter.unusedSectionVars false in
theorem coordMap_basisFun (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W)
    (i : Fin n) : coordMap e c (Pi.basisFun K (Fin n) i) = c i := by
  simp [coordMap, Pi.single_apply, apply_ite e, ite_smul]

theorem normAt_one (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (c : OrthonormalBasis (Fin n) ℂ W) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (fun _ => 1) (InfinitePlace.mk e) x = ‖coordMap e c x‖ := by
  have h1 : coordMap e c x = c.repr.symm (WithLp.toLp 2 (fun i => e (x i))) := by
    rw [← c.sum_repr_symm]; rfl
  rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  simp [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

end Std

end GlobalTheory.ProvRowSide

end
