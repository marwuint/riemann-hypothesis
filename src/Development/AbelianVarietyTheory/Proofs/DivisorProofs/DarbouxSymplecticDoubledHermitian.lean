import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblEvalLaw

open Matrix

section Swap

variable {A : Type} [CommRing A] {β m' : Type} [Fintype β] [DecidableEq β] [Fintype m'] [DecidableEq m']

def midSwap (e : m' ⊕ m' ≃ β) : β ⊕ β ≃ β ⊕ β :=
  (e.sumCongr e).symm.trans ((Equiv.sumSumSumComm m' m' m' m').trans (e.sumCongr e))

variable (e : m' ⊕ m' ≃ β)

@[simp] theorem midSwap_inl_inl (i : m') : midSwap e (.inl (e (.inl i))) = .inl (e (.inl i)) := by simp [midSwap]
@[simp] theorem midSwap_inl_inr (i : m') : midSwap e (.inl (e (.inr i))) = .inr (e (.inl i)) := by simp [midSwap]
@[simp] theorem midSwap_inr_inl (i : m') : midSwap e (.inr (e (.inl i))) = .inl (e (.inr i)) := by simp [midSwap]
@[simp] theorem midSwap_inr_inr (i : m') : midSwap e (.inr (e (.inr i))) = .inr (e (.inr i)) := by simp [midSwap]

theorem midSwap_midSwap (x : β ⊕ β) : midSwap e (midSwap e x) = x := by
  rcases x with x | x <;> obtain ⟨i | i, rfl⟩ := e.surjective x <;> simp

theorem midSwap_symm : (midSwap e).symm = midSwap e :=
  Equiv.ext fun x => by rw [Equiv.symm_apply_eq, midSwap_midSwap]

def swapMat : Matrix (β ⊕ β) (β ⊕ β) A := (midSwap e).toPEquiv.toMatrix

theorem swapMat_mul {γ : Type} (M : Matrix (β ⊕ β) γ A) : swapMat e * M = M.submatrix (midSwap e) id :=
  PEquiv.toMatrix_toPEquiv_mul _ _

theorem mul_swapMat {γ : Type} (M : Matrix γ (β ⊕ β) A) : M * swapMat e = M.submatrix id (midSwap e) :=
  (PEquiv.mul_toMatrix_toPEquiv M (midSwap e)).trans (by rw [midSwap_symm])

theorem swapMat_mul_self : swapMat (A := A) e * swapMat e = 1 := by
  refine (swapMat_mul e (swapMat e)).trans ?_
  ext x y
  simp [swapMat, PEquiv.toMatrix_apply, midSwap_midSwap, Matrix.one_apply]

theorem swapMat_transpose : (swapMat (A := A) e)ᵀ = swapMat e := by
  ext x y
  simp only [swapMat, transpose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  exact propext ⟨fun h => by rw [← h, midSwap_midSwap], fun h => by rw [← h, midSwap_midSwap]⟩

theorem swapMat_map (f : A → A) (h0 : f 0 = 0) (h1 : f 1 = 1) : (swapMat (A := A) e).map f = swapMat e := by
  ext x y
  simp only [swapMat, map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp [h0, h1]

theorem dbl_submatrix_midSwap (J : Matrix m' m' A) :
    (WeilM.dbl (blkMat e J (-J))).submatrix (midSwap e) (midSwap e) = WeilM.dbl (blkMat e J (-J)) := by
  ext x y
  rcases x with x | x <;> obtain ⟨i | i, rfl⟩ := e.surjective x <;>
    rcases y with y | y <;> obtain ⟨j | j, rfl⟩ := e.surjective y <;>
    simp [WeilM.dbl, blkMat]

end Swap

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

open Matrix

section Elts

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {β m' : Type} [Fintype β] [DecidableEq β] [Fintype m'] [DecidableEq m'] (e : m' ⊕ m' ≃ β)

def swapU (J : Matrix m' m' A) : UG c (WeilM.dbl (blkMat e J (-J))) :=
  ⟨⟨swapMat e, swapMat e, swapMat_mul_self e, swapMat_mul_self e⟩, by
    show (swapMat e)ᵀ * WeilM.dbl (blkMat e J (-J)) * (swapMat e).map c = WeilM.dbl (blkMat e J (-J))
    rw [swapMat_transpose, swapMat_map e _ (map_zero c) (map_one c)]
    refine (congrArg (· * swapMat e) (swapMat_mul e _)).trans ((mul_swapMat e _).trans ?_)
    rw [submatrix_submatrix]
    exact dbl_submatrix_midSwap e J⟩

variable {c} in

def leftU {J : Matrix β β A} (g : UG c J) : UG c (WeilM.dbl J) :=
  ⟨⟨fromBlocks (g : GL β A).1 0 0 1, fromBlocks (g⁻¹ : GL β A).1 0 0 1,
    by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩, by
    show (fromBlocks (g : GL β A).1 0 0 1)ᵀ * fromBlocks J 0 0 (-J) * (fromBlocks (g : GL β A).1 0 0 1).map c =
      fromBlocks J 0 0 (-J)
    have hg : ((g : GL β A) : Matrix β β A)ᵀ * J * ((g : GL β A) : Matrix β β A).map c = J := g.2
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hg, Matrix.map_one _ (map_zero c) (map_one c)]⟩

variable {c} in
theorem val_leftU {J : Matrix β β A} (g : UG c J) :
    ((leftU g : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (g : GL β A).1 0 0 1 := rfl

end Elts

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

end GlobalTheory.DblEvalLaw
