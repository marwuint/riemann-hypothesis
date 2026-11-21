import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S IsDedekindDomain
open Classical ValuativeRel

def piO {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) (ϖ : 𝒪[F]) : L.O :=
  ⟨algebraMap F E ϖ, (L.O_def _).2 (by
    rw [show algebraMap F E (ϖ : F) = algebraMap 𝒪[F] E ϖ from
      (IsScalarTower.algebraMap_apply 𝒪[F] F E ϖ).symm]
    exact isIntegral_algebraMap)⟩

def FLocO : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1) ∧
      (∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O) ∧
      (∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)

def FResField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (Ideal.span {piO L ϖ}).IsMaximal ∧
      Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 ∧
      ∀ x y : L.O, (y : E) = L.cj x →
        Ideal.Quotient.mk (Ideal.span {piO L ϖ}) y =
          Ideal.Quotient.mk (Ideal.span {piO L ϖ}) x ^ Nat.card 𝓀[F]

def FLatBasis : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), IsNonarchimedeanLocalField F →
    CharZero F → (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1

end PI.UnitaryGroupMassFormula.CntFormula
