import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ConeComplexBaseChange

variable {σ : Type} [Fintype σ]

omit [Fintype σ] in

theorem map_int_complex_eq :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

theorem comap_of_minimal (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco

theorem dim_cancel_one {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]

end ConeComplexBaseChange

end GroundTheory.Heights₂.Heights.Targets
