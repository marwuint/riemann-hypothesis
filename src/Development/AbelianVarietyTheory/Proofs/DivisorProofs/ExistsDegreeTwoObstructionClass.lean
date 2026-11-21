import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsComp
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isOb2 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w
  have hθ : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ θ : Ω[F.obj T⁄R₀] →+ L.B T'',
      IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) θ := by
    intro T T' T'' a b
    obtain ⟨θ, hθ, -⟩ := (theta_classify R R₀ (L.B T) (F.obj T) (L.B T'') I hI π hπ (L.p T) (L.semi T)
      (L.surj T) (L.ker T) ((L.ρ b).comp (L.ρ a))).1 (L.ρ (a ≫ b)) (fun x ↦ by
        rw [← L.ker T'', map_sub, AlgHom.comp_apply, L.nat, L.nat, L.nat, mp_comp, sub_self])
    exact ⟨θ, hθ⟩
  choose θ hθ using hθ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    _root_.GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = θ T T' T'' a b (w.1 T) := fun T T' T'' a b ↦
    (_root_.GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
      (L.ker T'') (σ T'') (hσ T'')).2.2.2 _ ((hθ T T' T'' a b).mem _)
  choose z hzK hzσ using hz
  have key : ∀ (T T' T'' T''' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T''') (x : Ω[F.obj T⁄R₀]),
      L.ρ c (θ T T' T'' a b x) + θ T T'' T''' (a ≫ b) c x =
        θ T T' T''' a (b ≫ c) x + θ T' T'' T''' b c (p1 F a x) := by
    intro T T' T'' T''' a b c x
    have h1 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T'') (L.B T''') _ _ _
      (hθ T T' T'' a b)).1 (L.ρ c)
    have s1 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h1).2.1 (hθ T T'' T''' (a ≫ b) c)
    have h2 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T''') (L.B T''') _ _ _
      (hθ T' T'' T''' b c)).2 (L.ρ a) (mp F a) (L.nat a)
    have s2 := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h2).2.1 (hθ T T' T''' a (b ≫ c))
    rw [Category.assoc] at s1
    rw [AlgHom.comp_assoc] at s2
    have e := (_root_.GlobalTheory.Obs.isTheta_add R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ (L.ρ (a ≫ b ≫ c)) _ _ s1).2.2.1 s2
    have ex := DFunLike.congr_fun e x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at ex
    exact ex.trans (add_comm _ _)
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := _root_.GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply _root_.GlobalTheory.Obs.sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add, k1, k2, k3, k4, sub_self, add_zero]
    · rw [em, map_sub, map_add, map_add, ← (nat.1 _), hzσ, hzσ, hzσ, hzσ, w.2 a, key, sub_self]
  exact ⟨H2.mk _ ⟨_, hZ⟩, θ, σ, ⟨_, hZ⟩, hθ, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, hzσ T T' T'' a b⟩⟩

end GlobalTheory.Obs
