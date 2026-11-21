import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOverFieldAxesWedge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLocalFiniteLengthAndSocleElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveOfAxesVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePullHO2OfPullHO1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibrePullH1Abelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem artinian_pullHO_surjective : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w) := by
  intro R _ _ _ A _ g hA hsm k _ σ hσ X₀ s₀ ψ w
  have FF := _root_.GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge
  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], Module.length R R ≤ n →
      ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
        (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R _ _ _ hlen A _ g hA hsm
      by_cases hF : IsField R
      · refine ⟨?_, _root_.GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 R A (FF R hF A g hA hsm).1⟩
        intro k _ σ hσ X₀ s₀ ψ w
        letI := hF.toField
        exact _root_.GlobalTheory.AbCoh.pullHO1_surjective_of_bijective R k σ ⟨σ.injective, hσ⟩ _ _ X₀ s₀ ψ w
      · obtain ⟨t, ht0, htm, hlt⟩ := (_root_.GlobalTheory.artinianLocal_finiteLength_and_socle_element R).2 hF
        obtain ⟨n0, hn0⟩ := (_root_.GlobalTheory.artinianLocal_finiteLength_and_socle_element R).1
        have htop : Ideal.span {t} ≠ ⊤ := by
          intro h
          have hu : IsUnit t := by simpa [Ideal.span_singleton_eq_top] using h
          apply hF
          have hm : IsLocalRing.maximalIdeal R = ⊥ := by
            rw [eq_bot_iff]; intro a ha
            have := htm a ha
            simpa [hu.mul_left_eq_zero] using this
          exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hm
        haveI : Nontrivial (R ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 htop
        haveI : IsLocalRing (R ⧸ Ideal.span {t}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        obtain ⟨n1, hn1⟩ := (_root_.GlobalTheory.artinianLocal_finiteLength_and_socle_element (R ⧸ Ideal.span {t})).1
        have hlt' : n1 < n := by
          rw [hn0, hn1] at hlt; rw [hn0] at hlen
          exact lt_of_lt_of_le (by exact_mod_cast hlt) (by exact_mod_cast hlen)
        have IH := ih n1 hlt' (R ⧸ Ideal.span {t}) (le_of_eq hn1)
        exact ⟨_root_.GlobalTheory.AbCoh.SmallStepSurj.surj_of_smallExt R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ IH B g hB hs) A g hA hsm,
          _root_.GlobalTheory.AbCoh.StepPrim.main R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ (IH B g hB hs).2) A g hA hsm⟩
  obtain ⟨n, hn⟩ := (_root_.GlobalTheory.artinianLocal_finiteLength_and_socle_element R).1
  have h1 := (key n R (le_of_eq hn) A g hA hsm).1 k σ hσ X₀ s₀ ψ w
  exact ⟨h1, _root_.GlobalTheory.AbCoh.pullHO2_surjective_of_wedge _ _ _ _ _ _ _ _ w.w h1 (_root_.GlobalTheory.AbCohWedgeLift.wedgeO_fibre FF R A g hA hsm k σ X₀ s₀ ψ w)⟩

end GlobalTheory.AbCoh
