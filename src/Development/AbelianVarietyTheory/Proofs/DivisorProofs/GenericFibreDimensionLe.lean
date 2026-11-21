import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenFibreDim

section

attribute [local instance low] specializationOrder

theorem le_height_of_specializingMap {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T0Space X] [T0Space Z] {f : X → Z} (hf : SpecializingMap f) (n : ℕ) :
    ∀ y : X, (n : ℕ∞) ≤ Order.height (f y) → (n : ℕ∞) ≤ Order.height y := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hex : ∃ b < f y, (n : ℕ∞) ≤ Order.height b := by
      by_contra hne
      push_neg at hne
      have h1 : Order.height (f y) ≤ n := by
        rw [Order.height_eq_iSup_lt_height]
        exact iSup₂_le fun b hb => Order.add_one_le_of_lt (hne b hb)
      have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ n := hy.trans h1
      have h3 : n + 1 ≤ n := by exact_mod_cast h2
      omega
    obtain ⟨b, hb, hnb⟩ := hex
    obtain ⟨y', hyy', rfl⟩ := hf hb.le
    have hlt : y' < y := lt_of_le_of_ne hyy' (fun h => hb.ne (by rw [h]))
    have h4 := Order.height_add_one_le hlt
    have h5 := ih y' hnb
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.height y' + 1 := by gcongr
      _ ≤ Order.height y := h4

end

end GlobalTheory.GenFibreDim
