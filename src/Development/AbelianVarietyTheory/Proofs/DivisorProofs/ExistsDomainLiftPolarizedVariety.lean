import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSiegPre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero

noncomputable section

namespace GlobalTheory.SiegPt

section Level

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp unitOn omegaStd IsGrpPullback LBIso pushPt)

theorem sec_bijective {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] (X : Over (Sp O)) [IsProper X.hom]
    (e : Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  have he : e.left = Geo.Tor.spMap (algebraMap O C) := (Category.comp_id _).symm.trans (Over.w e)
  have hE : ValuativeCriterion.Existence X.hom := by
    have h : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness X.hom := IsSeparated.valuativeCriterion X.hom
  let S : (Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ X) → ValuativeCommSq X.hom := fun z =>
    { R := O, K := C, i₁ := z.left, i₂ := 𝟙 _, commSq := ⟨(Over.w z).trans (Category.comp_id _).symm⟩ }
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h₁ : Geo.Tor.spMap (algebraMap O C) ≫ x.left = (e ≫ x).left := congrArg (· ≫ x.left) he.symm
    have h₂ : Geo.Tor.spMap (algebraMap O C) ≫ y.left = (e ≫ x).left :=
      (congrArg (· ≫ y.left) he.symm).trans (congrArg Over.Hom.left hxy.symm)
    have := (hU (S (e ≫ x))).elim ⟨x.left, h₁, Over.w x⟩ ⟨y.left, h₂, Over.w y⟩
    exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
  · obtain ⟨⟨l, h1, h2⟩⟩ := hE (S z)
    refine ⟨Over.homMk l h2, Over.OverMorphism.ext ?_⟩
    show e.left ≫ l = z.left
    rw [he]
    exact h1

theorem exists_secHom {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] {Q : Out.PolAV (Sp O)}
    {Q' : Out.PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left}
    (H : IsGrpPullback Q'.A Q.A (Geo.Tor.spMap (algebraMap O C)) ψ) (hw' : LBIso Q'.L (Q.L.pull ψ)) :
    ∃ ρ : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (𝟙_ (Over (Sp C)) ⟶ Q'.A), Function.Bijective ρ ∧
      ∀ (n : ℕ) x y (u : Oˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map (algebraMap O C).toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  have := Q.isAb.proper
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let β := algebraMap O C
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H
  let e : Over.mk (Geo.Tor.spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (Geo.Tor.spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (Over.mk (Geo.Tor.spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = Geo.Tor.spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.bijective.comp (sec_bijective Q.A e), fun n x y u hx hy hw => ?_⟩
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (IsFractionRing.injective O C h₅)
  exact hc

theorem exists_level {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (P : Out.PolAV (Sp O)) (h M : ℕ) (ze : Oˣ) (hg : P.g = h) (hM : IsUnit (M : O))
    (hz : IsPrimitiveRoot (algebraMap O C ze) M) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp O)) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
      (∀ x, lev x ^ M = 1) ∧ ∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  subst hg
  have hM' : (M : C) ≠ 0 := by
    have := (hM.map (algebraMap O C)).ne_zero
    rwa [map_natCast] at this
  haveI : NeZero M := ⟨fun h0 => hM' (by rw [h0, Nat.cast_zero])⟩
  obtain ⟨P', g, hg, hgg, hmul, tw, htw⟩ :=
    GlobalTheory.laws_without_cohomology.2.2.1 _ _ (Geo.Tor.spMap (algebraMap O C)) P
  have hp : IsGrpPullback P'.A P.A (Geo.Tor.spMap (algebraMap O C)) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  obtain ⟨ρ, hρ, hw⟩ := exists_secHom hp (Geo.Tor.LBIso.symm ⟨tw, htw⟩)
  obtain ⟨lev⟩ := nonempty_level_of_isAlgClosed C P' M (Units.map (algebraMap O C).toMonoidHom ze) hM'
    (IsPrimitiveRoot.coe_units_iff.1 hz)
  rw [← hgg]
  have := P'.isAb.comm
  choose t ht using fun a : Fin P'.g ⊕ Fin P'.g → ℤ =>
    hρ.2 (LevelCompare.homOfBasis lev (Multiplicative.ofAdd (fun j => (a j : ZMod M))))
  have tors : ∀ a, t a ^ M = 1 := fun a => hρ.1 (by rw [map_pow, ht, map_one, LevelCompare.hom_pow])
  refine ⟨t, fun a b => hρ.1 ?_, tors, fun a b => hw M _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, ← map_mul, ← ofAdd_add]
    exact congrArg _ (congrArg _ (funext fun j => Int.cast_add _ _))
  · rw [ht, ht, map_zpow]
    have w := LevelCompare.pairing_of_basis lev a b
    unfold unitOn at w ⊢
    rw [map_zpow]
    exact w

end Level

end GlobalTheory.SiegPt

end
