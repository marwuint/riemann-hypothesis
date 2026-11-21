import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal

noncomputable section

open scoped Matrix NNReal TensorProduct Classical Topology
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont
open GlobalTheory.Core.Rk.SWLaw (zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.RegularEisensteinLemmas

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

structure IsSum (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E) : Prop where
  tt : jTᴴ * T'.gram * jT = T.gram
  oo : j₀ᴴ * T'.gram * j₀ = -T₀.gram
  ot : j₀ᴴ * T'.gram * jT = 0
  rank_add : T.rank + T₀.rank = T'.rank

end PositivityTheory.RegularEisensteinLemmas
