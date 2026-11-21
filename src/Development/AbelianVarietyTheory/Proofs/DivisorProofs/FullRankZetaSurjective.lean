import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Matrix Topology

noncomputable section

namespace GlobalTheory.FullRankOnto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

local notation "Yo" => GlobalTheory.FullRankCoinv.Y0 k n d

def blkEquiv (hnd : n ≤ d) : Fin (d - n) ⊕ Fin n ≃ Fin d :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hnd))

def blkMat (hnd : n ≤ d) : Matrix (Fin n) (Fin n) k →* Matrix (Fin d) (Fin d) k where
  toFun M := reindex (blkEquiv hnd) (blkEquiv hnd) (fromBlocks 1 0 0 M)
  map_one' := by simp [fromBlocks_one]
  map_mul' A B := by
    simp only [reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
    simp

def blkGL (hnd : n ≤ d) : GL (Fin n) k →* GL (Fin d) k := Units.map (blkMat hnd)

theorem blkGL_val (hnd : n ≤ d) (g : GL (Fin n) k) :
    (blkGL hnd g).val = reindex (blkEquiv hnd) (blkEquiv hnd) (fromBlocks 1 0 0 g.val) := rfl

end GlobalTheory.FullRankOnto
