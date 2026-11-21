import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetDatumVectorFiniteHeisenbergCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.DictFree

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable def conjQ : Qbar →+* Qbar where
  toFun x := ⟨starRingEnd ℂ x, by
    have h : IsAlgebraic ℚ (x : ℂ) := (mem_algebraicClosure_iff).1 x.2
    exact (mem_algebraicClosure_iff).2
      (h.algHom ((Complex.conjAe.restrictScalars ℚ : ℂ ≃ₐ[ℚ] ℂ) : ℂ →ₐ[ℚ] ℂ))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

noncomputable def oppQ {T : Type} : Pair T → (Qbar →+* Qbar)
  | .chi _ _ => conjQ
  | .core _ => conjQ
  | _ => RingHom.id _

theorem oppQ_coe {T : Type} (p : Pair T) (x : Qbar) : ((oppQ p x : Qbar) : ℂ) = opp p (x : ℂ) := by
  cases p <;> rfl

theorem opp_opp {T : Type} (p : Pair T) (z : ℂ) : opp p (opp p z) = z := by
  cases p <;> simp [opp]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem jetTab_comb {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    (B : VertexFrames G) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) {n : ℕ}
    (a : Fin n → ℂ) (w : Fin n → WO (G.pS p) (G.pT p)) (hw : ∀ i, (w i).map (infPart D) = 0)
    (X : FinPt G p.small) (Y : FinPt G p.big) (mon : Formalism.L2.Ker.DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ) :
    jetTab W B p (∑ i, a i • heisO W.ψ _ _ (w i) f) X Y mon = ∑ i, a i * jetTab W B p (heisO W.ψ _ _ (w i) f) X Y mon := by
  have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf n a w hw (monomial (mon.mapDomain (fvar G p)) 1)).1
  have h2 : ∀ i, heisO W.ψ _ _ (w i) (pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f
      (monomial (mon.mapDomain (fvar G p)) 1)) = pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p)
      (G.onT B p) (heisO W.ψ _ _ (w i) f) (monomial (mon.mapDomain (fvar G p)) 1) := fun i => by
    have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
      (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf 1 (fun _ => 1) (fun _ => w i) (fun _ => hw i)
      (monomial (mon.mapDomain (fvar G p)) 1)).1
    simpa using this
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO]
  rw [← h1]
  simp only [← h2, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem differentiable_U {D : D7} (Tr : Tor D) {N N' : ℕ} (s : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.U D Tr s G) := by
  unfold Formalism.MainNotions.TaylorLogMetric.U Formalism.MainNotions.TaylorLogMetric.Hf
  fun_prop

end GlobalTheory.DictFree

end
