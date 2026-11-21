import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1

theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
