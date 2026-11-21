import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

universe u

theorem corr_of_corr_pullGen {X Y Z : Scheme.{u}} (L : LB X) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (φ' : I' → (Y ⟶ X)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (h : Z ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (hc : ∀ a b : Y ⟶ X, h ≫ a = h ≫ b → a = b)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  intro j j' c₁ c₂ c₃
  have e := H j j' (fun a b e => c₁ a b (hc _ _ e)) (fun a b e => c₂ a b (hc _ _ e))
    (fun a b e => c₃ a b (hc _ _ e))
  have le : h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have e' := congrArg (res le) e
  change res le (res _ (LB.ts (LB.pullGen L _ _ t h) j)) = res le (res _ (LB.ts (LB.pullGen L _ _ t' h) j')) at e'
  rw [LB.ts_pullGen, LB.ts_pullGen] at e'
  simp only [LB.res_res] at e'
  refine Units.map_injective (f := (h.app (LB.wchart L φ j ⊓ LB.wchart L φ' j')).hom.toMonoidHom)
    (hinj _) ?_
  exact (LB.pullU_res h _ _).trans (e'.trans (LB.pullU_res h _ _).symm)

theorem corr_of_generic_of_isSeparated
    (V : Type u) [CommRing V] (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [IsSeparated G.hom]
    (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    (L : LB G.left) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (T.left ⟶ G.left)) (ε : I → ℤ) (φ' : I' → (T.left ⟶ G.left)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (H : LB.Gen.Corr L _ _ _ _
      (LB.pullGen L _ _ t (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))
      (LB.pullGen L _ _ t' (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  have := (ExtUnique.spec_fractionRing V K).2
  have : IsSchemeTheoreticallyDominant
      (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :=
    .of_isPullback (IsPullback.of_hasPullback _ _).flip
  refine corr_of_corr_pullGen L φ ε φ' ε' t t' _ (fun U => Scheme.Hom.app_injective _ U)
    (fun a b e => ?_) H
  exact ExtUnique.hom_ext_of_dominant (G.hom ≫ terminal.from _) (terminal.hom_ext _ _) _ e

namespace DoubledPoint

variable {X : Scheme.{0}} (U : X.Opens)

instance {i j : WalkingSpan} (f : i ⟶ j) : IsOpenImmersion ((span U.ι U.ι).map f) := by
  rcases f with _ | (_ | _) <;> (dsimp; infer_instance)

end DoubledPoint

end GlobalTheory
