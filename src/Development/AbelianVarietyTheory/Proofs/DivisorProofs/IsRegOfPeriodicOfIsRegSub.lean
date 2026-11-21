import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocally
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedSubalgebraRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularSectionOfRegularDifferences
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexAbelianVarietySectionRatioAffineCov
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfPeriodicRegularDifferencesRatioCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_periodic_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ i, IsReg u.ex (W i) (h i) := by
  intro A _ g L u hA K W h hW hd hp hr
  obtain ⟨hopen, -, hpre, hval, hinf, -, hsup, -, -, -, -, htop⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  have glue := _root_.GlobalTheory.CechPer.isReg_of_locally A g L u hA
  have alg := _root_.GlobalTheory.RegAlg.main A g L u
  obtain ⟨n, V, r, hV⟩ := _root_.GlobalTheory.RatioCover.main A g L u hA
  have tor := fun c : Fin n => _root_.GlobalTheory.CechPer.exists_section_of_isReg_sub A g L u hA K W h hW hr ⟨V c, hV.1 c⟩
  choose k hk using tor
  have hk' : ∀ c i, IsReg u.ex (V c ⊓ W i) (k c - h i) := hk
  have covW : ∀ z, ∃ i, z ∈ pre u.ex (W i) := fun z => (hsup K W z).1 (hW ▸ htop z)
  have covV : ∀ z, ∃ c, z ∈ pre u.ex (V c) := fun z => (hsup (Fin n) V z).1 (hV.2.1 ▸ htop z)
  have hreg : ∀ c, IsReg u.ex (V c) (k c) := by
    refine _root_.GlobalTheory.CechPer.isReg_of_isReg_sub A g L u hA n V r hV k (fun c z hz => ?_) (fun c l z hz => ?_) (fun c c' => ?_)
    · obtain ⟨i, hi⟩ := covW z
      have hz' : z ∈ pre u.ex (V c ⊓ W i) := by rw [hinf]; exact ⟨hz, hi⟩
      have h1 : DifferentiableAt ℂ (k c - h i) z :=
        ((alg _).2.2.2.2.1 _ (hk' c i) z hz').differentiableAt ((hopen _).mem_nhds hz')
      have h2 : DifferentiableAt ℂ (h i) z := (hd i z hi).differentiableAt ((hopen _).mem_nhds hi)
      have h3 := h1.add h2
      rw [sub_add_cancel] at h3
      exact h3.differentiableWithinAt
    · obtain ⟨i, hi⟩ := covW z
      have hz' : z ∈ pre u.ex (V c ⊓ W i) := by rw [hinf]; exact ⟨hz, hi⟩
      obtain ⟨b, hb⟩ := hk' c i
      have e1 := hb z hz'
      have e2 := hb _ ((hpre _ l z).2 hz')
      rw [hval, ← e1, Pi.sub_apply, Pi.sub_apply, hp i l z hi] at e2
      exact sub_left_injective e2
    · refine glue _ _ fun z hz => ?_
      obtain ⟨i, hi⟩ := covW z
      refine ⟨V c ⊓ V c' ⊓ W i, inf_le_left, by rw [hinf]; exact ⟨hz, hi⟩, ?_⟩
      have r1 := (alg _).2.2.2.1 (V c ⊓ V c' ⊓ W i) (inf_le_inf_right _ inf_le_left) _ (hk' c i)
      have r2 := (alg _).2.2.2.1 (V c ⊓ V c' ⊓ W i) (inf_le_inf_right _ inf_le_right) _ (hk' c' i)
      have r3 := ((alg _).2.1 _ _ r1 r2).2.1
      rwa [sub_sub_sub_cancel_right] at r3
  intro i
  refine glue _ _ fun z hz => ?_
  obtain ⟨c, hc⟩ := covV z
  refine ⟨V c ⊓ W i, inf_le_right, by rw [hinf]; exact ⟨hc, hz⟩, ?_⟩
  have r1 := (alg _).2.2.2.1 (V c ⊓ W i) inf_le_left _ (hreg c)
  have r3 := ((alg _).2.1 _ _ r1 (hk' c i)).2.1
  rwa [sub_sub_cancel] at r3

end GlobalTheory.CechPer
