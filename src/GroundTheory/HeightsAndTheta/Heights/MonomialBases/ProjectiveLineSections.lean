import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry NumberField TensorProduct GroundTheory.Arith.SchemeCoh Matrix
open ProjScheme SectionsLatticeFS

noncomputable section

namespace ProjectiveLineSections

def expo (n k : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (n - k)

@[simp] lemma expo_zero (n k : ℕ) : expo n k 0 = k := by simp [expo]

@[simp] lemma expo_one (n k : ℕ) : expo n k 1 = n - k := by simp [expo]

variable (hfin : SectionsLattice.Finite.Statement) (hl2 : SectionsLattice.L2.Statement)
  (hflat : PNFlat.Statement.{0}) (hred : PNReduced.Statement.{0})
  (hf : FSContinuousFrame.Statement.{0}) (hc : FSNormConj.Statement.{0})
  (hs : FSFullSupport.Statement) (hci : FSConjInvariant.Statement)

end ProjectiveLineSections

end

end GroundTheory.Heights₂.Heights
