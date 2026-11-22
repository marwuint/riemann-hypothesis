import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.SphInertRef

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}

theorem rt_real_eq_of_lev (hMA : MtAd Y M) (i : Fin D.R.m) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1))
    (κ : GAf D.host.E D.R.nV)
    (hJ : (hMA.PV i).ψ κ ∈ Formalism.IndefR.Links.levS _ (R.toRealDat.βV i)
      (Formalism.IndefR.RecTie.datVP R.toRealDat i (Y.tupT D.what₂.mu0) (R.toRealDat.levR F.lv2 false)))
    (hχ : Formalism.IndefR.Lev.levChi _ (R.toRealDat.βV i)
      (Formalism.IndefR.RecTie.datVP R.toRealDat i (Y.tupT D.what₂.mu0) (R.toRealDat.levR F.lv2 false)) ((hMA.PV i).ψ κ) = 1) :
    NG.rt D.host.E D.R.nV κ ((M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x) =
      (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x := by
  have h0 : Formalism.IndefR.RecTie.Used0 D D.what₂.mu0 := Or.inl rfl
  funext g
  apply (hMA.eW _ h0 i).injective
  have e1 := hMA.read _ h0 i x (g * κ)
  have e2 := hMA.read _ h0 i x g
  have e3 := (Y.IL.jMt _ h0 i x).2.2 _ hJ ((hMA.PV i).ψ g)
  rw [hχ, ← map_mul] at e3
  exact e1.trans (e3.trans ((one_smul ℂ _).trans e2.symm))

end Read

end GlobalTheory.SphInertRef

end
