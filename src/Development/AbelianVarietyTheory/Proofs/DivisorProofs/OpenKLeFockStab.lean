import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum

open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)
noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
