import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.d_ob : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := _root_.GlobalTheory.CompanionTheory.TiltFacts.obFacts

theorem CrystallineSemistableComparison.RL.acris_mod_l_base_change : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := GlobalTheory.T.acris_level_one_facts

theorem CrystallineSemistableComparison.RL.d_seq : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := _root_.GlobalTheory.CompanionTheory.LSeq.racrSeq
