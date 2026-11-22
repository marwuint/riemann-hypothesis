import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  obtain ⟨t, ht⟩ := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
    ext <;> simp [x3]
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
    have h := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) k
    rw [e] at h
    refine Eq.trans ?_ (h.symm.trans (Finset.prod_congr rfl fun I _ =>
      congrArg (fun q => k q ^ thε I) (Category.id_comp _)))
    simp [Fin.prod_univ_eight]) t ht
  exact ⟨t', ht'⟩

theorem isGrpPullback_prod {S S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨isPullback_prod m.1 n.1 h₁ h₂, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (grpMor_prod (κ := dp0 ℤ) (κ' := dp0 ℤ) (σ := RingHom.id ℤ) (t := specZIsTerminal.from _) (t' := specZIsTerminal.from _)
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, m.1.w, m.2⟩
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, n.1.w, n.2⟩ h₁ h₂).mul T x y x₀ y₀ hx hy

theorem lift_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {x y : T ⟶ G} {N : ℕ} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : lift x y ^ N = 1 := by
  ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, hx, hy]

section Level

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

end Level

end GlobalTheory.WeilIntegral
