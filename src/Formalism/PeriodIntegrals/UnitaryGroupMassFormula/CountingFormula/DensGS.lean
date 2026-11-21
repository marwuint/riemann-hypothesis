import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

def SplitCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝓀[F])
          (Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]),
          IsUnit Ph.det ∧ Gm.rank = Fintype.card ι ∧
          H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
              ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
            (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι) Ph Gm : ℝ)

def OSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F →
    ∀ (e : E ≃ₐ[F] F × F) (x : E), x ∈ L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]

def IsSplitCoord {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} (e : E ≃ₐ[F] F × F)
    {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : Prop :=
  (∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) ∧
  (∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) ∧
  IsUnit Ph.det ∧
  ∀ x y : V, e (H.h x y) =
    (∑ k, ∑ l, (π x).1 k * (Ph k l : F) * (π y).2 l, ∑ k, ∑ l, (π y).1 k * (Ph k l : F) * (π x).2 l)

def CoordData : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (e : E ≃ₐ[F] F × F), (∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
        (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]), IsSplitCoord e H Λ π Ph

end PI.UnitaryGroupMassFormula.CntFormula
