import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}}

section Basis

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def localBasis (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z) :
    divisorSections D U :=
  ⟨fun _ => ((g⁻¹ : (X.functionField)ˣ) : X.functionField), by
    refine ⟨fun y => ⟨⊤, trivial, fun _ _ => rfl⟩, fun y hy => ?_⟩
    rw [PrimeDivisor.valuation_le_exp_iff _ (Units.ne_zero _)]
    have h1 := PrimeDivisor.ord_mul (PrimeDivisor.ofPoint y.1 hy) (Units.ne_zero g)
      (Units.ne_zero g⁻¹)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one,
      hg (PrimeDivisor.ofPoint y.1 hy) y.2] at h1
    dsimp only
    omega⟩

theorem localBasis_bijective (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z)
    (V : X.Opens) (hVU : V ≤ U) :
    Function.Bijective (fun r : Γ(X, V) => r • divisorSectionsRes D hVU (localBasis D U g hg)) := by
  by_cases hne : Nonempty V
  · constructor
    · intro r₁ r₂ h12
      obtain ⟨y⟩ := hne
      have : Nonempty V := ⟨y⟩
      have := congrArg (fun t : divisorSections D V => t.1 y) h12
      have h := mul_right_cancel₀ (Units.ne_zero g⁻¹) this
      rw [sectionValue_eq V y r₁, sectionValue_eq V y r₂] at h
      exact Scheme.germToFunctionField_injective X V h
    · intro t
      obtain ⟨y0⟩ := hne
      have : Nonempty V := ⟨y0⟩
      set c := t.1 y0
      have hord : ∀ Z : PrimeDivisor X, Z.point ∈ V →
          0 ≤ Z.ord (c * (g : X.functionField)) := by
        intro Z hZ
        by_cases hc : c = 0
        · rw [hc, zero_mul, PrimeDivisor.ord_zero]
        · rw [PrimeDivisor.ord_mul Z hc (Units.ne_zero g), hg Z (hVU hZ)]
          have ht := t.2.2 ⟨Z.point, hZ⟩ Z.2
          have hcZ : t.1 ⟨Z.point, hZ⟩ = c := divisorSections_apply_eq D t _ y0
          rw [hcZ] at ht
          have := (PrimeDivisor.valuation_le_exp_iff Z hc (D Z)).mp ht
          omega
      obtain ⟨r, hr⟩ := exists_section_of_ord_nonneg V _ hord
      refine ⟨r, Subtype.ext (funext fun y => ?_)⟩
      rw [divisorSections_smul_apply, sectionValue_eq, hr, divisorSections_apply_eq D t y y0]
      change c * (g : X.functionField) * ((g⁻¹ : (X.functionField)ˣ) : X.functionField) = c
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · have hV : V = ⊥ := by
      ext y
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hne ⟨⟨y, hy⟩⟩
    have : Subsingleton Γ(X, V) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun t => ⟨0, Subtype.ext (funext fun y => ?_)⟩⟩
    exact (hne ⟨y⟩).elim

end Basis

end GroundTheory.Arith.SchemeCoh
