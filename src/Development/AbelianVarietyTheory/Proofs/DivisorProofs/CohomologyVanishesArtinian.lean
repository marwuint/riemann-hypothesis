import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionToSiegelDomain

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishes_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ), (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian
