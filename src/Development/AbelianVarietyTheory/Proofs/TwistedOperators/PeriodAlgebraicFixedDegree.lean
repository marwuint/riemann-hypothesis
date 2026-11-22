import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameGramUnitaryIdentity

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

theorem conj_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p, hp, ?_⟩
  have := Polynomial.aeval_algHom_apply ((starRingEnd ℂ).toRatAlgHom) z p
  rw [hz, map_zero] at this
  simpa using this

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem jet_negSp_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (u : WO S T) (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT (heisO ψ (negSp S) T u f) (MvPolynomial.monomial k 1) 0 =
      starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (fun w => starRingEnd ℂ (f w)))
        (MvPolynomial.monomial k 1) 0) := by
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT BS BT _ hψ hθ k 0]
  have h := ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 u (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)).2
  have hcc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcc] at h
  have key : (fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w)) = heisO ψ S T u (fun w => starRingEnd ℂ (f w)) := by
    have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f = fun w => starRingEnd ℂ (f w) := rfl
    rw [h, ← hcj]
    funext w
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [key]

theorem std_eq_colLat_one {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotTransJet

namespace GlobalTheory.BotTransJet

end GlobalTheory.BotTransJet
