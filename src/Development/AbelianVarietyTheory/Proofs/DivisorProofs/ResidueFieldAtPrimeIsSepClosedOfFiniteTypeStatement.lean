import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteType

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType
