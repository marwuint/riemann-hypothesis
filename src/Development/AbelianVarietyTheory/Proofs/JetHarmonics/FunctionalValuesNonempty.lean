import Mathlib
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeastExponentCompare

open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem (bar balancedForms quad IsPosSemidef IsPosDef Exponent pairing pairingValues IsPhiC)
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (IsBalancedSpace evalSum)
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement (outer IsPosHerm)

variable {E : Type} [Field E] [NumberField E]

theorem finite_projective_iff (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    (Module.Finite (𝓞 E) Y ∧ Module.Projective (𝓞 E) Y) ↔ (Module.Finite ℤ Y ∧ Module.Free ℤ Y) := by
  constructor
  · rintro ⟨hf, hp⟩
    have hfin : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
    have hfl : Module.Flat ℤ Y := Module.Flat.trans ℤ (𝓞 E) Y
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hf, hfr⟩
    exact ⟨Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Y, GlobalTheory.PointStepCompare.projective_of_free E⟩

variable [IsCMField E] {cj : E → E}

def IsConj (cj : E → E) : Prop := ∀ c : 𝓞 E, cj c = IsCMField.complexConj E (c : E)

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem isBalancedSpace (h : IsConj cj) : IsBalancedSpace E (SymB cj Y) := by
  intro β
  change ((∀ a b, β a b = β b a) ∧ ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun a x y => hb a _ ?_ x y⟩
    rw [h a, IsCMField.coe_ringOfIntegersComplexConj]
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun c c' hc x y => ?_⟩

    have hc' : c' = IsCMField.ringOfIntegersComplexConj E c := by
      apply RingOfIntegers.ext
      rw [hc, h c, IsCMField.coe_ringOfIntegersComplexConj]
    rw [hc']
    exact hb c x y

variable (Y) in

def formsEquiv (h : IsConj cj) : SymB cj Y ≃ₗ[ℝ] balancedForms E Y where
  toFun β := ⟨AddMonoidHom.mk' (fun x => ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x).toAddMonoidHom)
      (fun x x' => by ext y; simp),
    ((isBalancedSpace h _).1 β.2).1, ((isBalancedSpace h _).1 β.2).2⟩
  invFun β := ⟨LinearMap.mk₂ ℤ (fun x y => β.1 x y) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp),
    (isBalancedSpace h _).2 ⟨β.2.1, β.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def Admissible (l : SymB cj Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β

def functionalValues (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ x = l b}

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem functionalValues_nonempty (h : IsConj cj) (b : SymB cj Y) : (functionalValues b).Nonempty := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨l, hi, hp⟩ := GlobalTheory.PointStepCompare.exists_admissible E (isBalancedSpace (Y := Y) h)
  exact ⟨l b, l, ⟨hi, hp⟩, rfl⟩

end GlobalTheory.LeastExponentCompare

end
