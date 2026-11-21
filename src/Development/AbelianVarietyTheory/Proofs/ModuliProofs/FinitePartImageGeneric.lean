import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff

noncomputable section

namespace GlobalTheory.FinitePartGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem exists_normal_factor (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] (ψ : A →+* F)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap (FractionRing R) F (algebraMap R _ r)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (a : A →+* R'), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map (a.comp (algebraMap R A)) ≤ maximalIdeal R' ∧
      ∀ y, algebraMap (FractionRing R') F (algebraMap R' _ (a y)) = ψ y := by
  obtain ⟨h₁, -, h₃, h₄⟩ := hR
  letI : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ' : A →ₐ[R] F := { ψ with commutes' := hψ }
  have hi : ∀ y, IsIntegral R (ψ y) := fun y => (Algebra.IsIntegral.isIntegral (R := R) y).map ψ'
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let L := IntermediateField.adjoin (FractionRing R) (ψ '' s)
  have : Finite (ψ '' s) := (s.finite_toSet.image ψ).to_subtype
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨y, -, rfl⟩; exact (hi y).tower_top)
  have hm : ∀ y, ψ y ∈ L := fun y => by
    have hy : y ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy => rw [Algebra.smul_def, map_mul, hψ]; exact mul_mem (L.algebraMap_mem _) hy
  obtain ⟨f₁, f₂, f₃, f₄, -⟩ := integralClosure_finite_local_of_isAdicComplete R h₄ L
  have : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let j : integralClosure R L →+* F := (algebraMap L F).comp (algebraMap _ L)
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  let a : A →+* integralClosure R L := (ψ.codRestrict L hm).codRestrict (integralClosure R L) fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R L F) Subtype.val_injective).1 (hi y)
  have ha : a.comp (algebraMap R A) = algebraMap R _ := RingHom.ext fun r => hj (hψ r)
  refine ⟨integralClosure R L, inferInstance, inferInstance, f₂, (IsFractionRing.lift (g := j) hj).toAlgebra, a,
    ⟨f₃, inferInstance, f₄, CompleteFiniteExtension.isAdicComplete_of_finite_local R _⟩, ?_,
    fun y => IsFractionRing.lift_algebraMap (g := j) hj _⟩
  rw [ha]
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) _ _ inferInstance

theorem exists_normal_point (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : Over (Sp R))
    [IsFinite N.hom] (x : Sp F ⟶ N.left) (hx : x ≫ N.hom = jFK (R := R) F ≫ jK R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (φ : R →+* R') (ξ : Sp R' ⟶ N.left), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map φ ≤ maximalIdeal R' ∧ ArcPull.Compat φ F ∧ ξ ≫ N.hom = spMap φ ∧
      (jFK (R := R') F ≫ jK R') ≫ ξ = x := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ N.left.isoSpec.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have e : φ ≫ ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hx])
  have e' : ∀ r, ψ.hom (φ.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) e
  obtain ⟨R', i₁, i₂, i₃, i₄, a, h₁, h₂, h₃⟩ := exists_normal_factor R hR F Γ(N.left, ⊤) ψ.hom e'
  refine ⟨R', i₁, i₂, i₃, i₄, a.comp φ.hom, Spec.map (CommRingCat.ofHom a) ≫ N.left.isoSpec.inv, h₁, h₂,
    fun r => (e' r).symm.trans (h₃ _).symm, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h₃))

section Transport

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

theorem isPointOf_thru {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left}
    {g₀ : GtPt D.toPre T} {g : GtPt D'.toPre T'} (H : Thru hD.w hD.xe h g₀ g) {x₀ : T ⟶ G} {x : T' ⟶ G'}
    (hx : x.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = h ≫ x₀.left)
    (h₀ : IsPointOf U.toUnifPre g₀ x₀) : IsPointOf U'.toUnifPre g x := by
  intro e Z r y hy
  obtain ⟨wL, -, he, -, HU⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨k, hf, hpt, -⟩ := HU e
  have gp := pull_grp hD
  obtain ⟨cb, cv⟩ := (hasCoords_iff _ _ _ _ _).1 (h₀ e Z (r ≫ h) (y ≫ k) (by
    rw [Category.assoc, hf, ← Category.assoc, hy, Category.assoc, hx, Category.assoc]))
  have hy' : y ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom = r ≫ T'.hom := by
    rw [← Over.w (fstG I' e G'), ← Category.assoc, hy, Category.assoc, Over.w]
  let y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk y hy'
  let r' : Over.mk (r ≫ T'.hom) ⟶ T' := Over.homMk r rfl
  have hb : y ≫ (U'.gt e).pG.left = r ≫ g.b.left := gp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) hpt.1).trans ((Category.assoc _ _ _).symm.trans (cb.trans
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans (Category.assoc _ _ _).symm))))))
    (by rw [Category.assoc, Category.assoc, Over.w, Over.w]; exact hy')
  refine (hasCoords_iff _ _ _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
  have v := ConstFam.pmaps_val (hpt.2 χ).1 (hpt.2 χ).2 y hJ hJ'
  have eP : ∏ i, ConstFam.wVal hD.w z J J' (y ≫ D'.toPre.Oφ (U'.gt e).pG χ i) ^ Oinvε i =
      ∏ i, ConstFam.wVal hD.w z J J' (r ≫ DegPre.gtφT D'.toPre T' g.b χ i) ^ DegPre.gtε i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w z J J' q ^ DegPre.gtε i)
      (comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb) χ i)
  rw [eP] at v
  exact mul_left_cancel (v.symm.trans ((cv _ z J hJ).trans ((H χ).2 _ r z J J' hJ hJ')))

theorem isPullGtF_thru {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {T : Over (Sp R)} {T' : Over (Sp R')}
    {h : T'.left ⟶ T.left} {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru hD.w hD.xe h g₀ g) {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] {σ : Sp F ⟶ T'.left} {q : GtPtF D F}
    {q' : GtPtF D' F} (hq : GtPt.IsPullF F (σ ≫ h) g₀ q) (hq' : GtPt.IsPullF F σ g q') : IsPullGtF φ hD F q q' := by
  have m := FieldRestrictionTest.maps_eq hq
  have m' := FieldRestrictionTest.maps_eq hq'
  have hψ : ∀ χ i, DegPre.gtφ D' F q'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F q.b (hD.xe χ) i := fun χ i => by
    rw [m, m', Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ((H χ).1 i)).trans (Category.assoc _ _ _).symm)
  refine ⟨(hψ 0 2).trans (Category.id_comp _), fun χ => ⟨hψ χ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB
    D'.P.isLB _ (q'.isGen χ) _ (q.isGen _) (hψ χ) fun y J J' hJ hJ' => ?_⟩⟩
  have a := (val_corr hJ (hq.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)
  have a' := (val_corr hJ' (hq'.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
  rw [Category.id_comp] at a a'
  refine a.trans (((H χ).2 _ σ y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ a'.symm))
  exact Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w y J J' q ^ DegPre.gtε i) (m' χ i).symm

end Transport

end GlobalTheory.FinitePartGeneric
