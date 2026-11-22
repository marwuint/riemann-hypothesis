import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁ θ₀ hθ
  by_cases hz : ∀ α j, (F₁.f α).f j = 0
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => ?_⟩
    obtain ⟨a, b, ha, hb, h⟩ := hθ W T
    exact ⟨a, a, 1, ha, ha, _root_.GlobalTheory.Mum.ZeroFam.exp_of_members_zero R hR D C W T 1 le_rfl θ₀ F₁ hz a b h a, by simp⟩
  push_neg at hz
  obtain ⟨G, S, hG, hS⟩ := _root_.GlobalTheory.Mum.exists_mulPull R hR D C m hm F₁ θ₀
  have hGz := hG hz
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  swap
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩
  obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
  obtain ⟨a₀, b₀, ha₀, hb₀, h₀⟩ := hθ W₀ T₀
  obtain ⟨v₀, hv₀⟩ := hS W₀ T₀ a₀ b₀ ha₀ h₀
  obtain ⟨r, t, hr, ht, hrt⟩ := _root_.GlobalTheory.Mum.exists_ratio_of_exp_one_trait R hR D C (m ^ 2) hk G S (Φ G) (fun W _ _ _ T => (hΦ W T).imp fun u hu => hu G)
    W₀ T₀ a₀ (b₀ * v₀) ha₀ (mul_ne_zero hb₀ v₀.ne_zero) hv₀
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hθ W T
  obtain ⟨v, hv⟩ := hS W T a b ha h
  obtain ⟨u, hu⟩ := hrt W T
  have htW : T.φ t ≠ 0 := fun h0 => ht (T.inj (h0.trans (map_zero _).symm))
  have h1 := _root_.GlobalTheory.Mum.Trait.exp_mul_left R D C W T (m ^ 2) S G a (b * v) (T.φ t) hv
  have h2 := _root_.GlobalTheory.Mum.Trait.exp_mul_left R D C W T (m ^ 2) S G (T.φ t) (T.φ r * u) a hu
  rw [mul_comm a (T.φ t)] at h2
  have he := _root_.GlobalTheory.Mum.Trait.exp_unique R hR D C W T (m ^ 2) hk S G hGz (T.φ t * a) _ _ (mul_ne_zero htW ha) h1 h2
  refine ⟨a, b, u * v⁻¹, ha, hb, h, ?_⟩
  have : b * T.φ t * v = a * T.φ r * u := by linear_combination he
  calc b * T.φ t = b * T.φ t * v * ↑v⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [this]; push_cast; ring

end GlobalTheory.Mum
