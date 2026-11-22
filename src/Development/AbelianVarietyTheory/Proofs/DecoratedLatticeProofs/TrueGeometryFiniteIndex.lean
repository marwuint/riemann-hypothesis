import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Fam.MidLoc

theorem nonempty_colCh {D : D7} (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Nonempty (ColCh u C) := GlobalTheory.Fam.TopLocFac.nonempty_colCh u C

theorem nonempty_rowCh {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ) (hc : R.IsChain) (u : D.what₂.Word)
    (g : Fam.Geo D) (t : T) : Nonempty (RowCh R P u g t) :=
  ⟨{ vP := fun _ => 0, vT := fun _ _ => 0, io := fun _ => 0, ioT := fun _ _ => 0
     sBF := fun j ρ h => FamInhab.mkStep _ _ (hc.ωY t j (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes j ρ h).d)
       (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j ρ h).d) (g.vol (j + 1)) ρ ρ
     sFB := fun j σ h => FamInhab.mkStep _ _ (hc.ωY t (j + 1) (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j (σ + 1) h).d)
       (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes (j + 1 + 1) σ (idx_step h)).d) (g.vol (j + 1 + 1)) (σ + 1) σ }⟩

end GlobalTheory.Fam.MidLoc
