import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijective

open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := GlobalTheory.LKTrip.HTGroup.bijective_locP
