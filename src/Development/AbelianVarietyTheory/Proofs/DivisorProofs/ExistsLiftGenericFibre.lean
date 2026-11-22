import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep.Setup

def RootsIn {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) (F : Polynomial V) : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (ψ : V₁ →+* D) (d : D), F.eval₂ (ψ.comp ρ) d = 0 → d ∈ ψ.range

theorem rootsIn_of_splits {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) {F : Polynomial V} (hF : F.Monic)
    (h : (F.map ρ).Splits) : RootsIn ρ F := by
  intro D _ _ ψ d hd
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 h
  rw [← Polynomial.eval₂_map, hm, (hF.map ρ).leadingCoeff, map_one, _root_.one_mul, Polynomial.eval₂_multiset_prod,
    Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  obtain ⟨a, -, ha⟩ := hd
  exact ⟨a, (sub_eq_zero.1 (by simpa using ha)).symm⟩

theorem exists_ext (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V) (L : Type) [Field L]
    [Algebra (FractionRing V) L] [FiniteDimensional (FractionRing V) L] (F : Polynomial V) (hF : F.Monic) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (σ : L →+* FractionRing V₁),
      GlobalTheory.Mum.Base V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧
      (σ.comp (algebraMap (FractionRing V) L)).comp (algebraMap V _) = (algebraMap V₁ _).comp ρ ∧ RootsIn ρ F := by
  haveI := hV.2
  let K := FractionRing V
  let F₁ : Polynomial L := F.map ((algebraMap K L).comp (algebraMap V K))
  let L₂ := F₁.SplittingField
  haveI : FiniteDimensional K L₂ := Module.Finite.trans L L₂
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := MumLevel.exists_galois_root K L₂ 1 le_rfl
  obtain ⟨V₁, _, _, _, ρ, e, -, hρ, he, -, -⟩ := MumLevel.exists_ring V hV E ζ 1 le_rfl hζ
  let τ : L₂ →+* FractionRing V₁ := e.toRingHom.comp j.toRingHom
  have hσ : ((τ.comp (algebraMap L L₂)).comp (algebraMap K L)).comp (algebraMap V K) = (algebraMap V₁ _).comp ρ :=
    RingHom.ext fun r => (congrArg e ((congrArg j (IsScalarTower.algebraMap_apply K L L₂ _).symm).trans
      (j.commutes _))).trans (he r)
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  haveI := hρ.1.2.2.1
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, τ.comp (algebraMap L L₂),
    ⟨hρ.1, (ρ.charZero_iff hρ.2.1).1 inferInstance⟩, hρ.2.1, hρ.2.2, hσ, rootsIn_of_splits ρ hF ?_⟩
  refine Polynomial.Splits.of_splits_map_of_injective hinj ?_ fun a ha => ?_
  · have := (Polynomial.SplittingField.splits F₁).map τ
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hσ] at this
    rwa [Polynomial.map_map]
  · exact IsIntegrallyClosed.isIntegral_iff.1 ⟨F.map ρ, hF.map ρ, by
      rw [← Polynomial.eval_map]; exact (Polynomial.mem_roots'.1 ha).2⟩

theorem RootsIn.exists_sq {V V₁ : Type} [CommRing V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {F : Polynomial V}
    (h : RootsIn ρ F) {s : V} (hs : Polynomial.X ^ 2 - Polynomial.C s ∣ F) : ∃ r : V₁, r ^ 2 = ρ s := by
  let D := AlgebraicClosure (FractionRing V₁)
  let ψ : V₁ →+* D := (algebraMap (FractionRing V₁) D).comp (algebraMap V₁ _)
  have hψ : Function.Injective ψ := (algebraMap (FractionRing V₁) D).injective.comp (IsFractionRing.injective V₁ _)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (ρ s)) two_pos
  obtain ⟨G, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := h D ψ d (by simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, hd])
  exact ⟨r, hψ (by rw [map_pow, hd])⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_lift_genericFibre (C : UCompact Xo c) {O W : Type} [CommRing O] [CommRing W] (ev : O →+* W) [IsLocalHom ev]
    (t : Sp O ⟶ C.Z) (ξ : Sp W ⟶ pullback C.z (spMap C.b)) (h : spMap ev ≫ t = ξ ≫ pullback.fst _ _) :
    ∃ ζ : Sp O ⟶ pullback C.z (spMap C.b), ζ ≫ pullback.fst _ _ = t := by
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ C.z)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (ξ ≫ pullback.snd _ _)
  have e : φ ≫ CommRingCat.ofHom ev = CommRingCat.ofHom C.b ≫ β := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hβ, ← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (φ.hom a) := fun a => by
    refine (isUnit_map_iff ev _).1 ?_
    rw [show ev (φ.hom a) = β.hom (C.b a) from congrArg (fun χ => χ.hom a.1) e]
    exact (IsLocalization.map_units c.F a).map β.hom
  refine ⟨pullback.lift t (spMap (IsLocalization.lift (S := c.F) hu)) ?_, pullback.lift_fst _ _ _⟩
  rw [← hφ, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsLocalization.lift_comp (S := c.F) hu).symm)

theorem fromSpecStalk_bot {X : Scheme.{0}} [IsIntegral X] (z : X) (p : Sp (X.presheaf.stalk z)) (hp : p.asIdeal = ⊥) :
    X.fromSpecStalk z p = genericPoint X := by
  obtain ⟨q, hq⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes z
  have h : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (show p.asIdeal ≤ q.asIdeal from hp ▸ bot_le)
  exact ((hq ▸ h.map (X.fromSpecStalk z).continuous).antisymm (genericPoint_specializes _)).eq

end GlobalTheory.USep.Setup
