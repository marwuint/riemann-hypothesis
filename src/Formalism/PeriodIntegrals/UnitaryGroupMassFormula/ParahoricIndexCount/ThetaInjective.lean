import Mathlib
import Formalism.PeriodIntegrals.ParahoricIdxZ
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure

noncomputable section

open Matrix

namespace PI.ParahoricIdxZ.W

section A

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

def theta {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin t) R)
    (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix (Fin (a + t)) (Fin (a + t)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

variable {ϖ}

end A

end PI.ParahoricIdxZ.W
