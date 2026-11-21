import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreWeilComm

variable {D : D7} {θ : InfFam D} {V : HSp D} {n : ℕ} {τ : D.what₂.Tau}

theorem continuous_of_mem (hθ : IsInfFam θ) {m : ℕ} (Φ : schwartzA θ m n) : Continuous Φ.1 :=
  (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)).1

theorem integrable_of_mem (hθ : IsInfFam θ) {m : ℕ} (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (Φ : schwartzA θ m n) :
    Integrable Φ.1 μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun t _ => map_add_right_eq_self μ t)
  obtain ⟨C, hC⟩ := hC N
  exact ((hN K hK).const_mul C).mono' hc.aestronglyMeasurable (.of_forall hC)

variable {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
  {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}

end GlobalTheory.RegSch.CentreWeilComm

end
