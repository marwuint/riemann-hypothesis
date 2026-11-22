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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinTransJet

theorem inV_stdL_eq_colLat {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

end GlobalTheory.FinTransJet

namespace GlobalTheory.FinTransJet

end GlobalTheory.FinTransJet
