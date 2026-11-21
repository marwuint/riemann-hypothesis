import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryHypotheses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThOInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.LineStab
theorem ptF_one' {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (f : WO V W → ℂ) : ptF ψ θ A B f 1 = f := by
  have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [h1]
  simp only [ptF, pureTensorO, pureTensorL]
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem thO_zero' {m k d : ℕ} {D : D7} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    GlobalTheory.TripleRead.thO Mo ψ G e 0 = 0 := by
  funext x
  simp only [GlobalTheory.TripleRead.thO, GlobalTheory.WeilM.thetaSum, Pi.zero_apply]
  refine (tsum_congr fun ξ => ?_).trans tsum_zero
  exact mul_zero _

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem det_sgn_gram {D : D7} (ε : Bool) (M : HSp D) (h : (GlobalTheory.RealDict.sgE (D := D) ε • M.gram).det ≠ 0) :
    ((sgn ε M).gram).det ≠ 0 := by
  have hg : (sgn ε M).gram = -(GlobalTheory.RealDict.sgE (D := D) ε • M.gram) := by
    cases ε <;> ext i j <;> simp [GlobalTheory.RealDict.sgE, sgn, HSpace.gram]
  rw [hg, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

end GlobalTheory.RealDict.LineStab

end
