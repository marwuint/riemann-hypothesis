import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualQOfTopInj
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem cardQ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ r : ℕ, Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) ∧ Nat.card (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r
  obtain ⟨⟨hO, hD, hF⟩, -⟩ := id hG
  have := hO
  have := hD
  have := hF
  have hq := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.1
  refine ⟨(GlobalTheory.CompanionTheory.LocDual.Q.finite_quot O A.V LA.T ϖ r hq LA.fg).2, ?_⟩
  have : Module.Finite O ↥LA.T := Module.Finite.iff_fg.mpr LA.fg
  have := LA.free
  rw [GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_free (Module.finBasis O ↥LA.T).equivFun,
    GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero, GlobalTheory.H1fGeneratorBoundAlt.finrank_lattice LA, pow_mul]

end PositivityTheory.LocalTateOrthogonality.Bk
