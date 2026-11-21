import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex

noncomputable section

abbrev E4 : Type := CyclotomicField 4 ℚ

instance : NumberField E4 := inferInstanceAs (NumberField (CyclotomicField 4 ℚ))

instance : IsCyclotomicExtension {4} ℚ E4 := by
  have h : @IsCyclotomicExtension {4} ℚ E4 _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

instance : IsCMField E4 := IsCyclotomicExtension.Rat.isCMField E4 (S := {4}) ⟨4, rfl, by norm_num⟩

def dim0 : (E4 →+* ℂ) → ℕ := fun _ => 0

instance : IsEmpty (Idx dim0) := ⟨fun i => i.2.elim0⟩

instance : Subsingleton (Vsp dim0) := ⟨fun x y => PiLp.ext fun i => isEmptyElim i⟩

instance : IsEmpty (Fin (2 * Fintype.card (Idx dim0))) :=
  ⟨fun i => absurd i.2 (by simp)⟩

theorem Hf0 (x y : Vsp dim0) : Hf x y = 0 := by
  simp [Hf]

def X0 : PT E4 where
  dim := dim0
  r := 0
  dim_conj := fun _ => rfl
  b := Module.Basis.empty _
  stable := fun α x _ => by rw [Subsingleton.elim (act α x) 0]; exact zero_mem _
  integral := fun _ _ _ _ => ⟨0, by simp [Hf0]⟩
  perfect := fun φ => ⟨0, zero_mem _, fun y => by
    have hy : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [hy, map_zero]; simp [Hf0]⟩
  eps := fun _ => 1
  eps_pm := fun _ _ => Or.inl rfl
  eps_add := fun _ _ _ _ => by simp [Hf0]
  eps_iso := fun _ _ _ => rfl

instance : IsEmpty (Idx X0.dim) := inferInstanceAs (IsEmpty (Idx dim0))

instance : Subsingleton (Vsp X0.dim) := inferInstanceAs (Subsingleton (Vsp dim0))

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
