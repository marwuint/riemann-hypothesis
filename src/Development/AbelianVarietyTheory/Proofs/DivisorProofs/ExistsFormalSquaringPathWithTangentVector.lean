import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPathFormallySmoothRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfLieSheafSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallySmoothStalkUnitSmoothGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwo

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_path_tan : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R] [Algebra ℚ R], Smooth G.hom → QuasiSeparated G.hom → ∀ (b : Sp R ⟶ S) (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∃ ξ, IsPath G 2 b ξ ∧ HasTan G b ξ τ w := by
  intro S G _ R _ _ _ hsm hqs b n V τ w hbV
  set s : S := b (IsLocalRing.closedPoint R)
  set β : S.presheaf.stalk s →+* R := (Scheme.stalkClosedPointTo b).hom
  have hβ : Spec.map (CommRingCat.ofHom β) ≫ S.fromSpecStalk s = b :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk b
  obtain ⟨-, -, -, hev4, -, -, hev7⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  have hsV : s ∈ V := (hev4 R S b V).1 hbV
  obtain ⟨π, ε, m, hSD, hεπ, hmπ, hεm⟩ := _root_.GlobalTheory.Nef.stalkData_exists S G s
  have hfs := _root_.GlobalTheory.Nef.stalk_formallySmooth_of_smooth S G hsm s π ε m hSD
  have hm2 := _root_.GlobalTheory.Nef.sqr_sub_two_mem S G hqs s π ε m hSD
  obtain ⟨δ, hδ, hδπ, hδτ⟩ := _root_.GlobalTheory.Nef.exists_stalkDer_of_lie S G R s π ε m β n V hsV τ w hSD
  obtain ⟨ψ, hψπ, hψ0, hψ1, hψ2⟩ := _root_.GlobalTheory.Nef.exists_path_ring _ _ R π ε m β δ hfs hεπ hmπ hεm hm2 hδ hδπ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ G.left.fromSpecStalk (unitSec G s), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hSD.str, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψπ,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hβ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hSD.unit, ← Category.assoc, hβ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ2, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hSD.sq, Category.assoc]
  · intro U hU V' hV he hb f
    have hs' : s ∈ V' := (hev4 R S b V').1 hb
    have hp : unitSec G s ∈ U := he hs'
    obtain ⟨h₁, e₁⟩ := hev7 (PowerSeries R) G.left (unitSec G s) ψ U hp
    rw [show evAt _ hU f = evAt _ h₁ f from rfl, e₁, hψ1, hδτ U hp V' hV he hs' f]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    obtain ⟨h₂, e₂⟩ := hev7 R S s β V' hs'
    rw [← e₂]
    have key : ∀ {b₁ b₂ : Sp R ⟶ S} (_ : b₁ = b₂) (k₁ : ⊤ ≤ b₁ ⁻¹ᵁ V') (k₂ : ⊤ ≤ b₂ ⁻¹ᵁ V') (g : Γ(S, V')),
        evAt b₁ k₁ g = evAt b₂ k₂ g := by
      rintro _ _ rfl _ _ _; rfl
    exact key hβ h₂ hb _

end GlobalTheory.Nef
