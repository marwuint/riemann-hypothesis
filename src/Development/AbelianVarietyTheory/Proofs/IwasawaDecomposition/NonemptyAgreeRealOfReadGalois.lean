import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.BasicNotions.TH

namespace GlobalTheory.HeightCounting.Up.StandardFrameAgreement

theorem stdFrame_iff {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) :
    R3.StdFrame hF P ↔ GlobalTheory.NJoin.StdFrame hF P := by
  have key : ∀ {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2),
      R3.swapCast h = principalLevelFrame.tensCastR h := by
    intro E _ _ F1 F2 h
    subst h
    rfl
  unfold R3.StdFrame GlobalTheory.NJoin.StdFrame principalLevelFrame.StdPsi
  rw [key hF]

end GlobalTheory.HeightCounting.Up.StandardFrameAgreement
