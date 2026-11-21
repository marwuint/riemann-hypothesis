import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRoot

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

namespace GammaOnLevels

open PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem cancel_C {x a : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (ha : a ≠ 0) {g : O⟦X⟧}
    (h : C a * g ∈ Ideal.span {X - C x}) : g ∈ Ideal.span {X - C x} := by
  obtain ⟨c, t, rfl⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hx g
  have h2 : C (a * c) ∈ Ideal.span {X - C x} := by
    have e : C (a * c) = C a * ((X - C x) * t + C c) - (X - C x) * (C a * t) := by
      rw [map_mul]; ring
    rw [e]
    exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have h3 := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx h2
  have hc : c = 0 := (mul_eq_zero.1 h3).resolve_left ha
  rw [hc, map_zero, add_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem eval_eq_zero {x : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (r : Polynomial O)
    (h : (r : O⟦X⟧) ∈ Ideal.span {X - C x}) : r.eval x = 0 := by
  apply Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx
  have e := Polynomial.modByMonic_add_div r (Polynomial.X - Polynomial.C x)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at e
  generalize r /ₘ (Polynomial.X - Polynomial.C x) = d at e
  generalize r.eval x = c at e ⊢
  subst e
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C,
    Polynomial.coe_C] at h
  have e2 : (C c : O⟦X⟧) = (C c + (X - C x) * (d : O⟦X⟧)) - (X - C x) * (d : O⟦X⟧) := by ring
  rw [e2]
  exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end GammaOnLevels

end Formalism.MainNotions.N.Ln17
