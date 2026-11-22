import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompact

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_units_locally_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := GlobalTheory.OrbFinAf.topA
