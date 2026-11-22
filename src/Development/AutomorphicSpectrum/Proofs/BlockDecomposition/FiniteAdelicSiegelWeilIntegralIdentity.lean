import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOverLatticeQuotientLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummablePeriodicBoundByDenominator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicIntegralInvariantOpenSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFiniteAdelesDenseRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBounded
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem integrable_starLoc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ μ hμ ν hν Q hQ
  obtain ⟨hLC, hSC, hT2, -, -, -, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTR, -, hSC2, -, -, -, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)
  haveI := hTR
  haveI := hSC2
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))
  haveI : SecondCountableTopology (HermR (Af F) σ n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (HermR (Af F) σ n) := inferInstance
  obtain ⟨U, hUo, hUc, hUp⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Period.starLoc_periodic F E σ hCM M J n ψ hψ μ hμ Q hQ
  obtain ⟨C, t, ht, hb⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.finite_bound F E σ hCM M J hJ n ψ hψ μ hμ Q hQ
  obtain ⟨τ, hτ, hc⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open F E σ hCM n U hUo t ht
  have hs : (n : ℝ) < (M : ℝ) / 2 := by
    have : ((2 * n : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  have hsum := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow F E σ n (U.comap (hermIn (Af F) σ n)) t ht τ hτ hc
    (fun c => ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖) (fun _ => norm_nonneg _)
    (fun c l hl => by
      show ‖_‖ = ‖_‖
      rw [map_add, hUp _ _ hl]) C ((M : ℝ) / 2) hb (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow F E σ hCM n _ hs)
  exact _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic _ _ ν U hUo hUc (hermIn (Af F) σ n) (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite F E σ hCM n U hUo) _ (fun g u hu => hUp g u hu) hsum

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
