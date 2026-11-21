import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HaarOrderData
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.WeilBound.CoreStatements.TorusUniformisation.RepresentationHypotheses.HostNumDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.RT

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

structure Std (W : G.Weil) (μ₀ : T) : Prop where

  lev : L.Is μ₀

  size : GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions.SizeOK D

  host : PositivityTheory.HostN.HostNum D

  cc : D.host.ccK = ⊤

  rk : 2 * D.R.m + 1 < D.R.r

  split : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK

  pdeE : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
    (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

namespace Std

end Std

end GlobalTheory.CompanionTheory.Ar.RT

end
