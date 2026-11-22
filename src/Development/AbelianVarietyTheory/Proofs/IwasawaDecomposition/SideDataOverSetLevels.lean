import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up

def sideB_congr {D : D7} {cf cf' : CharFrame D} {Rw Rw' : RowSide D} {low low' : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig eig' : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e2 : Rw = Rw') (e3 : low = low') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL') (e7 : eig = eig')
    (e8 : θ = θ') (h : SideB D cf Rw low Pq S hL eig θ) : SideB D cf' Rw' low' Pq' S' hL' eig' θ' := by
  subst e1 e2 e3 e4 e5 e7 e8
  cases e6
  exact h

end GlobalTheory.HeightCounting.Up
