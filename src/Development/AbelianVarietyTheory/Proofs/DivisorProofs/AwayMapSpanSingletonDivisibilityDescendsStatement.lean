import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapSpanSingletonDivisibilityDescends

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.awayMap_span_singleton_divisibility_descends : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), (∀ a : A, algebraMap A C a ∈ Ideal.span {algebraMap A C g} → a ∈ Ideal.span {g}) → ∀ b : Localization.Away f, Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} → b ∈ Ideal.span {algebraMap A (Localization.Away f) g} := GlobalTheory.awayMap_descends_divisibility
