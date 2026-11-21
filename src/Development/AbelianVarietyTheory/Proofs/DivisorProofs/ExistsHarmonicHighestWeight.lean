import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExistsStatement

noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.HarmLift

theorem lemA : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W),
    (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := GlobalTheory.T.exists_fockHarmonic_representative

theorem lemB : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧
      KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := _root_.GlobalTheory.FockAlg.fin_harm

theorem lemC : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 →
    ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) →
      (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) →
      (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) →
      ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (hZ : IsKC Z) : IsKC (adjZ Z) := by
  intro a b hab
  rw [GlobalTheory.FockAdj.adjZ_apply, hZ b a (fun h => hab (by revert h; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock])),
    star_zero, mul_zero]

theorem trace_PC {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  simp only [Eab, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e; exact absurd h hcd
  · rfl

end GlobalTheory.HarmLift
