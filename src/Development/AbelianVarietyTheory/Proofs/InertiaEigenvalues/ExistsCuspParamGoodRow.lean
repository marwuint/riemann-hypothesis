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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspOfGoodRow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NodupIntShift

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

end GlobalTheory.RowCuspFromLift

end
