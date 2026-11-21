import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmulMemOfMemLocW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHost
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
import BuildAid.D3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.StdModel

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

section Ker

variable {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}

theorem stdKer_iff (t : KerEntTied ex) : I.StdKer l Z t ↔ I.StdKerTie l Z t :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩⟩

end Ker

end GlobalTheory.Mem.Col2.StdModel

end
