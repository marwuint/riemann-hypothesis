import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtale

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_prod_of_etale : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := GlobalTheory.etale_prod
