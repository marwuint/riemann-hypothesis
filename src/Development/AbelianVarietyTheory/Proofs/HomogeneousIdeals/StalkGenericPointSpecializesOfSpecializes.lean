import Mathlib

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace GlobalTheory

section ThetaShiftProofs

open PowerSeries

theorem exists_algHom_powerSeries_apply_X_of_isAdicComplete {O : Type*} [CommRing O] (I : Ideal O)
    [h : IsAdicComplete I O] {π : O} (hπ : π ∈ I) : ∃ ev : O⟦X⟧ →ₐ[O] O, ev X = π := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

noncomputable def powerSeriesPrimeX (O : Type u) [CommRing O] [IsDomain O] :
    Spec (CommRingCat.of O⟦X⟧) :=
  (⟨Ideal.span {X}, span_X_isPrime⟩ : PrimeSpectrum O⟦X⟧)

@[simp]
theorem powerSeriesPrimeX_asIdeal (O : Type u) [CommRing O] [IsDomain O] :
    (powerSeriesPrimeX O).asIdeal = Ideal.span {(X : O⟦X⟧)} := rfl

variable {Z : Scheme.{u}} {η ξ : Z} [IsDomain (Z.presheaf.stalk η)]
  [IsDiscreteValuationRing (Z.presheaf.stalk η)]
  {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

end ThetaShiftProofs

end GlobalTheory
