import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeQuotientCorrespondenceOfTorsionTranspor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveBijectiveRelationRowVecEqMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCorrespondenceTorsionRelationProperties

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem exists_torsion_matrix : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ h c₀ c₁ τ₀ τ₁ h₀ h₁ N _
  obtain ⟨a, b, c⟩ := _root_.GlobalTheory.RelTors.main K ι Λ₀ Λ₁ (Tr t) c₀ c₁ τ₀ τ₁
    (_root_.GlobalTheory.WpFam.TrIs.main K ι g t Λ₀ Λ₁ Ω₀ Ω₁ h) h₀ h₁ N
    (fun x y => ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ Tr t k k')
    (fun _ _ => Iff.rfl)
  exact _root_.GlobalTheory.RelLin.main N _ a b c

end GlobalTheory.WpFam
