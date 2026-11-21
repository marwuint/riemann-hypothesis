import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset ArithmeticFunction

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem finite_splitting_of_group : GFiniteSplit := by
  intro q _ χ x z hx hxz
  unfold Gchi Sz tailL cN
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊z⌋₊ := Icc_subset_Icc le_rfl (Nat.floor_le_floor hxz)
  have e1 : (∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn.2
      rw [min_eq_left ((one_le_div hn0).2 hle)]
    · intro n hn hn'
      rw [mem_Icc] at hn hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have : x < n := by
        by_contra hc
        exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
      rw [min_eq_right ((div_le_one hn0).2 this.le)]; simp
  rw [e1]
  have : ∀ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) - ((Λ n * min 1 (x / n) : ℝ) : ℂ) * χ (n : ZMod q) := by
    intro n _; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem twist_evaluation_formula : TwEval := by
  intro t θ q _ n
  by_cases hu : IsUnit (n : ZMod (t * q))
  · unfold tw
    rw [MulChar.mul_apply]
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu']
    have h1 : (ZMod.cast ((n : ZMod (t * q))) : ZMod t) = (n : ZMod t) := by
      have : (ZMod.castHom (Dvd.intro q rfl : t ∣ t * q) (ZMod t)) (n : ZMod (t*q)) = (n : ZMod t) := map_natCast _ n
      simpa using this
    have h2 : (ZMod.cast ((n : ZMod (t * q))) : ZMod q) = (n : ZMod q) := by
      have : (ZMod.castHom (Dvd.intro_left t rfl : q ∣ t * q) (ZMod q)) (n : ZMod (t*q)) = (n : ZMod q) := map_natCast _ n
      simpa using this
    rw [h1, h2]
    congr 1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [qc, legendreSym]
  · rw [MulChar.map_nonunit _ hu]
    have hc : ¬ n.Coprime (t * q) := fun h => hu ((ZMod.isUnit_iff_coprime n _).2 h)
    by_cases h1 : n.Coprime t
    · have h2 : ¬ n.Coprime q := fun h => hc (Nat.Coprime.mul_right h1 h)
      have : jacobiSym (n : ℤ) q = 0 := by
        have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
        rw [jacobiSym.eq_zero_iff_not_coprime]
        simpa [Int.gcd_natCast_natCast] using h2
      simp [this]
    · have : θ (n : ZMod t) = 0 := MulChar.map_nonunit _ (fun h => h1 ((ZMod.isUnit_iff_coprime n _).1 h))
      simp [this]

end Formalism.HermitianLattices.ZeroFreeRegionGL2
