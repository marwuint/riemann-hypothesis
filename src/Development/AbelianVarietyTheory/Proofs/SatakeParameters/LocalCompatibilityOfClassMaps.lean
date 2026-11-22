import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfBlockTypeVectorPadicIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf

end GlobalTheory.LocCompTy
