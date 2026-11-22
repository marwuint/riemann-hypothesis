import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EpsMeasFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.LocalFields.LocalZetaEpsilon
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

namespace RootOfUnityValuation

section Roots

def IsRoot (z : ℂˣ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

theorem IsRoot.mul {a b : ℂˣ} (ha : IsRoot a) (hb : IsRoot b) : IsRoot (a * b) := by
  obtain ⟨m, hm, h1⟩ := ha
  obtain ⟨n, hn, h2⟩ := hb
  have e1 : a ^ (m * n) = 1 := by rw [pow_mul, h1, one_pow]
  have e2 : b ^ (m * n) = 1 := by rw [Nat.mul_comm m n, pow_mul, h2, one_pow]
  exact ⟨m * n, Nat.mul_pos hm hn, by rw [mul_pow, e1, e2, one_mul]⟩

theorem IsRoot.inv {a : ℂˣ} (ha : IsRoot a) : IsRoot a⁻¹ := by
  obtain ⟨m, hm, h1⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h1, inv_one]⟩

theorem IsRoot.pow {a : ℂˣ} (ha : IsRoot a) (f : ℕ) : IsRoot (a ^ f) := by
  obtain ⟨m, hm, h1⟩ := ha
  exact ⟨m, hm, by rw [← pow_mul, Nat.mul_comm, pow_mul, h1, one_pow]⟩

end Roots

end RootOfUnityValuation

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
