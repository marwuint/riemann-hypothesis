import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInertStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount

end GlobalTheory.UnitOrbCount
