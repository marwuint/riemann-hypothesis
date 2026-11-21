import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueOfRayClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimeHostIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmFrameExistsWithJE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMapRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportedStateHeckeGaloisStageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGaloisStageFitsOfSameCentreActions

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def nOfLay {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : Lay0 (Dof x)) (hZ : L.ZOk) (hE : L.EtaOk) : NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := L.nd, ntw := L.ntw, naut := L.naut, nbc := L.nbc, nexp := L.nexp,
    ntypes := L.ntypes, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq, nth := L.nth, nbr := L.nbr, nbr_ind := L.nbr_ind,
    self_good := L.self_good, ntwbr := L.ntwbr, ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie,
    rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

theorem exists_pq_sel (B : Base) {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) :
    ∃ Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield B.host.E)) → PlE B.host,
      (∀ v, NG.OverPl (Pq v) v) ∧ Set.range Pq = Set.range I.sel :=
  ⟨I.sel, fun v => hI.sel_ok v, rfl⟩

end GlobalTheory.HeightCounting.Up

end
