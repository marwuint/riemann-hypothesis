import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  intro ψ hψ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  have hopen : IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
    rw [_root_.GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n]
    exact GlobalTheory.T.theta_open_mirabolic k ψ hψ (n + 1) _
  exact _root_.GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k (n + 1)) (mirChar k ψ n) hopen
    (_root_.GlobalTheory.CompanionTheory.BZMirExhaust.exhaust k (n + 1)) f g hf hg hfg

end GlobalTheory.CompanionTheory.BZMir
