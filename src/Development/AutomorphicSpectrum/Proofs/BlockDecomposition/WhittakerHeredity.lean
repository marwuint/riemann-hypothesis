import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionOpenCellModuloWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellLeviUnipotentConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnipotentSubgroupFiniteGeneration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolume

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem whitHeredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitHeredity k := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd X _ _ π hπ
  obtain ⟨J, hJs, hJ⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.OpenCoinv.openFns_whittaker k ψ hψ h N d hd (piTensor π) (isSmooth_piTensor hπ)
  obtain ⟨E⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.PiCoinv.twJacquet_piTensor_equiv π (fun a => unipB k (Fin (d a))) (fun a => whitChar ψ (d a))
  set T := twKer (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N) with hT
  set S := twKer (piTensor π) (unipM k d) (whitM d ψ) with hS
  let a : openFns d hd (piTensor π) →ₗ[ℂ] (IndSp (stdBlocks d hd) (piTensor π)) ⧸ T :=
    T.mkQ ∘ₗ (openFns d hd (piTensor π)).subtype
  let b : openFns d hd (piTensor π) →ₗ[ℂ] (⨂[ℂ] a, X a) ⧸ S := S.mkQ ∘ₗ J
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f₀, h0, h1⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.exists_open_congr k ψ hψ hψ1 h N d hd (piTensor π) f
    refine ⟨⟨f₀, h0⟩, ?_⟩
    exact ((Submodule.Quotient.eq T).2 (by simpa [neg_sub] using T.neg_mem h1))
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, rfl⟩ := hJs w
    exact ⟨f, rfl⟩
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext f
    simp only [a, b, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.subtype_apply]
    exact (hJ f).symm
  exact ⟨(a.quotKerEquivOfSurjective ha).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((b.quotKerEquivOfSurjective hb).trans E))⟩

end GlobalTheory.CompanionTheory.Rodier
