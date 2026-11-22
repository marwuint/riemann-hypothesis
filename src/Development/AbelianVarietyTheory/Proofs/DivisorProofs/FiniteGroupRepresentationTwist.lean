import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexification

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem typeSubspace_eq_iInf_ker {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] {n : ℕ}
    {Wσ : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) :
    A.typeP J0 lam0 = ⨅ p : J0, LinearMap.ker (A.ρ p - ((A.chi p * lam0 p : LLˣ) : LL) • LinearMap.id) := by
  ext F
  simp [Formalism.IndefR.Arith.FormsL.mem_typeP, Submodule.mem_iInf, sub_eq_zero]

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

end GlobalTheory.DefRead
