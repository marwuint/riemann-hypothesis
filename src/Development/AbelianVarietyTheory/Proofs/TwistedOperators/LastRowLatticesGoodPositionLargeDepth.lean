import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowZeroBasePointCarriesLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointMovesRowLatticesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosNormLineSelfDualAndTopLatticeSplitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsBesselLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsJacobiLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagCharacterPrimitiveRowTestMovedLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFlagCharPrimitiveMovedLatticeLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiBasePointCarriesRowLatticeLinesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCarriesFlagLinesRowPeriodSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLineMapKeepsLatticesLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowCharsUnramifiedOffTensorPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

set_option maxHeartbeats 800000 in

theorem shapeAt_big : Big fun ch => ShapeAt ch := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    ((((((((((((((_root_.GlobalTheory.RowShape.moves0).and GlobalTheory.T.vacuum_base_point_moves_row_lattices).and GlobalTheory.T.posNormLine_selfDual_and_topLattice_splits).and GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split).and _root_.GlobalTheory.RowShape.big_isSelfDualC_rowN).and GlobalTheory.T.gridRowMovedLattice_splits_bessel_largeDepth).and _root_.GlobalTheory.RowShape.rowN_monoAt).and _root_.GlobalTheory.RowShape.big_primAt_rowN).and _root_.GlobalTheory.RowShape.big_primAt_rowJac).and
      GlobalTheory.T.besselToJacobi_basePoint_carries_row_lattice_lines).and _root_.GlobalTheory.RowShape.cols_jacBes_rowN).and _root_.GlobalTheory.RowShape.big_last_rowN).and _root_.GlobalTheory.LastLineLat.kap_lastTau_latO).and _root_.GlobalTheory.LastRowUnram.chars_unram)
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmv0, hmvS⟩, htop⟩, hcore⟩, hsd⟩, hmB⟩, hmJ⟩, hpB⟩, hpJ⟩, hcBF⟩, hcFB⟩, hlast⟩, hkap⟩, hun⟩ := h
  have hmv : ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := fun t b hb j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hmv0 t b hb
    · exact hmvS t b hb j hj0 hj
  have hX : ∀ k, k ≤ D.R.m → IsSelfDualC (ch.G.V (.top k)) (ch.G.Λ (.top k)) := fun k hk =>
    (ch.G.isV (X := .top k) (by show k ≤ D.R.m; omega) (fun _ e => Node.noConfusion e)).sd
  refine ⟨GlobalTheory.RowShape.rowN ch.G, GlobalTheory.RowShape.coreL ch.G, GlobalTheory.RowShape.lineL D, GlobalTheory.RowShape.topL D, hmv, htop.1, htop.2,
    fun t M hM j σ hj vN v => ?_⟩
  obtain ⟨hLL, hN0, hO⟩ := hcore j σ hj
  refine ⟨hLL, hO v, ?_, ?_, ?_, ?_⟩
  · exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd j (by omega)
        sdV₀ := hN0
        sdW := hsd (j + 1) (by omega)
        sdW₀ := hX (j + 1) (by omega)
        monoV := hmB j σ hj v
        monoW := hmJ (j + 1) (by omega) σ (by omega) v
        prim := hpB j σ hj v
        cols := hcBF j σ hj v
        last := fun hσ a ha => hlast j σ hj v hσ a ha }
  · intro i hi hi'
    subst hi
    exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd i (by omega)
        sdV₀ := hX i (by omega)
        sdW := hsd (i + 1) (by omega)
        sdW₀ := hN0
        monoV := hmJ i (by omega) (σ + 1) (by omega) v
        monoW := hmB (i + 1) σ (by omega) v
        prim := hpJ i (by omega) (σ + 1) (by omega) v
        cols := hcFB i σ hi' v }
  · intro hσ w hw
    subst hσ
    exact hkap j (by omega) v w hw
  · exact fun hoff i hi => hun t v hoff i hi
end GlobalTheory.RowShape

end
