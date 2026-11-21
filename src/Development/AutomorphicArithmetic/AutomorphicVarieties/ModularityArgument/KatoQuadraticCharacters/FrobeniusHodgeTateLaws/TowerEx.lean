import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.towerEx :
    UpperTheory.V.Z.Kato.Joint.TowerEx := by
  intro Ω _ _ _ ε
  obtain ⟨T, -⟩ := _root_.GlobalTheory.FN.tower_exists Ω ε
  exact ⟨T⟩
