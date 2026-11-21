import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglands

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay.EigCopy

theorem eigTrue_congr {D : D7} {cf : CharFrame D} {Rw Rw' : RowSide D} {Sb : Finset (PlE D.host)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (h : Rw.locR = Rw'.locR) (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) :
    GlobalTheory.TwInputs.EigTrue D cf Rw' Sb eig := by
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [← h]
  exact hT

end GlobalTheory.RowTriple.Lay.EigCopy
