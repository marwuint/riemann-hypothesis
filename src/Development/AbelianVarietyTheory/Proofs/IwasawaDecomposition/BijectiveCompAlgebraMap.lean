import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TwistTop

theorem exists_homeomorph : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y) (σ : F →+* ℂ), ∃ Φ : CxPts Y.str σ ≃ₜ CxPts M.p (σ.comp (algebraMap (𝓞 F) F)), ∀ z, (Φ z).1 = z.1 ≫ M.j := fun F _ _ Y M σ => by
  have e : spMap σ ≫ spMap (algebraMap (𝓞 F) F) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← Spec.map_comp]; rfl
  have h₁ (z : CxPts Y.str σ) : (z.1 ≫ M.j) ≫ M.p = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, e]
  have h₂ : Continuous fun y : CxPts M.p (σ.comp (algebraMap (𝓞 F) F)) =>
      M.pb.lift y.1 (spMap σ) (y.2.trans e.symm) := by
    rw [(Points.isEmbedding_of_isPullback M.pb).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
    exact (Prod.ext (M.pb.lift_fst _ _ _) (M.pb.lift_snd _ _ _)).symm
  exact ⟨{ toFun := fun z => ⟨z.1 ≫ M.j, h₁ z⟩
           invFun := fun y => ⟨M.pb.lift y.1 (spMap σ) (y.2.trans e.symm), M.pb.lift_snd _ _ _⟩
           left_inv := fun z => Subtype.ext (M.pb.hom_ext (M.pb.lift_fst _ _ _)
             ((M.pb.lift_snd _ _ _).trans z.2.symm))
           right_inv := fun y => Subtype.ext (M.pb.lift_fst _ _ _)
           continuous_toFun := ((Points.continuous_comp M.j).comp continuous_subtype_val).subtype_mk h₁
           continuous_invFun := h₂.subtype_mk fun y => M.pb.lift_snd _ _ _ }, fun _ => rfl⟩

theorem bijective_comp_algebraMap (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => IsLocalization.ringHom_ext (S := F) (nonZeroDivisors (𝓞 F)) (j := σ) (k := τ) h, fun τ => ?_⟩
  have hi : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
    have : (n : ℂ) = 0 := (map_intCast τ n).symm.trans hn
    exact Int.cast_eq_zero.1 this
  exact ⟨IsFractionRing.lift (K := F) hi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hi a⟩

end GlobalTheory.TwistTop
