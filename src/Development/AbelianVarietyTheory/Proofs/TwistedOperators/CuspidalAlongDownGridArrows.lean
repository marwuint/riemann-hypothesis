import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSenderStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

end GlobalTheory.FlipRun
