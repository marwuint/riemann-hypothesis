import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace Domination

section Charts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

abbrev pullPow (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) (n : ℕ) (J : Chart x') :
    Submodule (chartRing S x' J) Ω :=
  ((pullSys (S := S) x x').pow n).sub J

theorem chartRing_eq_ampleBase {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing S x (singleChart hi) = ampleBase (S := S) x i := by
  apply le_antisymm
  · intro a ha
    exact mem_ampleBase_of_mem_chartRing hi ha
  · rw [ampleBase, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact (ratio (S := S) hi l).2

theorem isNoetherianRing_chartRing [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing S x (singleChart hi)) := by
  classical
  have hfg : (chartRing S x (singleChart hi)).FG := by
    rw [chartRing_eq_ampleBase hi, ampleBase]
    refine ⟨Finset.univ.image fun l => x l / x i, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : Algebra.FiniteType S (chartRing S x (singleChart hi)) := ⟨(Subalgebra.fg_top _).mpr hfg⟩
  exact Algebra.FiniteType.isNoetherianRing S _

variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)

end Charts

end Domination

end

end GroundTheory.Heights₂.Heights.Kleiman
