import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

theorem hTens_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.MixedLagr
