import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondActionOnHermitianChartClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClassStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

set_option maxHeartbeats 1600000 in

theorem TDat.laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  intro E K _ _ _ _ n S ST A T hS hA
  have h1 := _root_.GlobalTheory.Mem.Col2.LRank.ranks A T hS hA
  have h2 := _root_.GlobalTheory.Mem.Col2.fv_te_laws A T hS hA
  have h3 := _root_.GlobalTheory.Mem.Col2.diamond_action_on_classes A T hS hA
  have h4 := GlobalTheory.T.levelFunctional_dilated_class A T hS hA
  exact ⟨h1.1, h1.2, h2.2.1, h2.2.2, h3.1, h3.2.1, h4, h3.2.2⟩

end GlobalTheory.Mem.Col2
