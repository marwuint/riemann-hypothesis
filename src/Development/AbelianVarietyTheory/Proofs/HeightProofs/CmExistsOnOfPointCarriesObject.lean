import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmDatumFormSqrtNegDPurePeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CMExistsCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

section Triples

variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem sab_lbIso {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_ptEquiv {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x) :
    ∃ p : (Over.mk x' ⟶ t'.G) ≃* (Over.mk x ⟶ t.G), ∀ u, (p u).left = u.left ≫ m.φ :=
  LiePull.exists_pushEquiv m.cart (Over.mk x') x h.symm

theorem pt_ext {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {u v : T ⟶ t'.G.left} (h₁ : u ≫ m.φ = v ≫ m.φ)
    (h₂ : u ≫ t'.G.hom = v ≫ t'.G.hom) : u = v :=
  m.cart.1.hom_ext h₁ h₂

end Triples

section Extend

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem spMap_int (j : K →+* K') {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : σ'.comp j = σ) :
    spMap (σ'.comp (algebraMap (𝓞 K') K')) ≫ spMap (RingOfIntegers.mapRingHom j) =
      spMap (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [spMap_comp', ← h]
  rfl

theorem exists_cmObj_extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ p q) (j : K →+* K') (σ' : K' →+* ℂ)
    (h : σ'.comp j = σ) :
    ∃ (X' : CMObj H K' (RingOfIntegers.mapRingHom j ρ) σ' p q)
      (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
      (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
      X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := by
  set f := RingOfIntegers.mapRingHom j with hf
  have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
  choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
  obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
  have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
  choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
  have hpt := spMap_int j h
  refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K' j X.split |>.1
            ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
            A := A', B := B'
            typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
            typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
            typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
            hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
  · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
    have e := congrArg Over.Hom.left ((X.lin i).2 c)
    simp only [Over.comp_left] at e
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
      (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
  · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
    choose pA hA using fun b => exists_ptEquiv (a b) hpt
    obtain ⟨x, hx⟩ := X.onto (pB y)
    refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
    rw [hx, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    apply Over.OverMorphism.ext
    simp only [Function.comp_apply]
    rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
    erw [hφ]
    rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
  · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
      (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
      ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
    rw [hpt]
    exact X.weil i

end Extend

end GlobalTheory.CMExistsCompare
end
