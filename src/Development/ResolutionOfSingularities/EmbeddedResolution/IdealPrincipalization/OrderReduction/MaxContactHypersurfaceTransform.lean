module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isMaxContactHypersurface_of_eq_of_eq_of_eq (k : Type u) [Field k] {P : Scheme.{u}}
    {p p' : P ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.LocallyOfFiniteType p']
    {A A' H H' : P.IdealSheafData} {μ : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H')
    (h : IsMaxContactHypersurface k p A μ H) :
    IsMaxContactHypersurface k p' A' μ H' := by
  subst hp hA hH
  exact h

private theorem locallyOfFiniteType_of_smooth_morphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : AlgebraicGeometry.Smooth f) : AlgebraicGeometry.LocallyOfFiniteType f := by
  have := h
  infer_instance

private theorem isMaxContactHypersurface_congr (k : Type u) [instk : Field k] {P : Scheme.{u}}
    {p p' : P ⟶ Spec (CommRingCat.of k)}
    (i1 : AlgebraicGeometry.LocallyOfFiniteType p)
    (i2 : AlgebraicGeometry.LocallyOfFiniteType p')
    {A A' H H' : P.IdealSheafData} {μ : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H')
    (h : @IsMaxContactHypersurface k instk P p i1 A μ H) :
    @IsMaxContactHypersurface k instk P p' i2 A' μ H' := by
  subst hp hA hH
  exact h

private theorem isMaxContactHypersurface_comap_iso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] (e : X ≅ Y)
    [AlgebraicGeometry.LocallyOfFiniteType (e.hom ≫ q)]
    (A : Y.IdealSheafData) (m : ℕ) (H : Y.IdealSheafData)
    (h : IsMaxContactHypersurface k q A m H) :
    IsMaxContactHypersurface k (e.hom ≫ q) (A.comap e.hom) m (H.comap e.hom) := by
  have : AlgebraicGeometry.Smooth e.hom := inferInstance
  have hmax : maxContactIdeal k (e.hom ≫ q) (A.comap e.hom) m
      = (maxContactIdeal k q A m).comap e.hom := by
    rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate]
    exact derivIdealSheafIterate_comap k q e.hom (m - 1) A
  rw [isMaxContactHypersurface_iff] at h
  rw [isMaxContactHypersurface_iff]
  intro x
  obtain ⟨U, hU, hxU, hcase⟩ := h (e.hom.base x)
  refine ⟨(TopologicalSpace.Opens.map e.hom.base).obj U, hU.preimage_of_isIso e.hom, hxU, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hHU, hmc⟩
  · left
    constructor
    · have hd : Disjoint (⇑e.hom.base ⁻¹' orderAtLeastLocus A m) (⇑e.hom.base ⁻¹' (U : Set ↥Y)) :=
        hdisj.preimage _
      rwa [orderAtLeastLocus_comap_iso_hom_eq_preimage]
    · rw [restrictIdeal_comap, htop]
      simp
  · right
    refine ⟨n, EtaleChart.ofIso q e c, j, ?_, ?_⟩
    · rw [restrictIdeal_comap, hHU, EtaleChart.ofIso_coordIdeal]
    · rw [isMaxContactCoord_iff] at hmc
      rw [isMaxContactCoord_iff, EtaleChart.ofIso_coordIdeal, hmax, restrictIdeal_comap]
      exact Scheme.IdealSheafData.comap_mono _ hmc

theorem isMaxContactHypersurface_iteratedStrictTransform (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (H : S.scheme.IdealSheafData)
    (hH : @IsMaxContactHypersurface S.base _ S.scheme S.structMap hv.locallyOfFiniteType
      S.ideal S.mult H)
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : ℕ) (ht : t ≤ u.length)
    [AlgebraicGeometry.LocallyOfFiniteType (u.proj t ≫ S.structMap)] :
    IsMaxContactHypersurface S.base (u.proj t ≫ S.structMap) (u.ideal t) S.mult
      (MaxContactReduction.iteratedStrictTransform u H t) := by
  have hlft : ∀ i : ℕ, i ≤ u.length →
      AlgebraicGeometry.LocallyOfFiniteType (u.proj i ≫ S.structMap) := by
    intro i hi
    have hsm : AlgebraicGeometry.Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec i) :=
      MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups i
        (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hi)
    rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec] at hsm
    exact locallyOfFiniteType_of_smooth_morphism hsm
  have key : ∀ i : ℕ, i ≤ u.length →
      ∀ inst : AlgebraicGeometry.LocallyOfFiniteType (u.proj i ≫ S.structMap),
        @IsMaxContactHypersurface S.base _ _ (u.proj i ≫ S.structMap) inst
          (u.ideal i) S.mult (MaxContactReduction.iteratedStrictTransform u H i) := by
    intro i
    induction i with
    | zero =>
        intro _ inst
        have hiso : AlgebraicGeometry.LocallyOfFiniteType (u.isoZero.hom ≫ S.structMap) := by
          rwa [← u.proj_zero]
        refine isMaxContactHypersurface_congr S.base hiso inst ?_ (u.ideal_zero).symm
          (MaxContactReduction.iteratedStrictTransform_zero u H).symm
          (@isMaxContactHypersurface_comap_iso S.base _ _ _ S.structMap hv.smooth
            hv.locallyOfFiniteType u.isoZero hiso S.ideal S.mult H hH)
        rw [u.proj_zero]
    | succ j ih =>
        intro hj inst
        have hjl : j < u.length := hj
        have instj : AlgebraicGeometry.LocallyOfFiniteType (u.proj j ≫ S.structMap) :=
          hlft j (le_of_lt hjl)
        have instsj : AlgebraicGeometry.LocallyOfFiniteType (u.toMarkedSequenceOfBlowups.projectionToSpec j) := by
          rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
        have instsj1 : AlgebraicGeometry.LocallyOfFiniteType
            (u.toMarkedSequenceOfBlowups.projectionToSpec (j + 1)) := by
          rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
        have hlt : j < u.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
          rwa [MarkedBlowupSequenceData.toMarkedSequence_length]
        have hadm := isMaxContactHypersurface_congr S.base instj instsj
          (MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec u j).symm
          (MarkedBlowupSequenceData.toMarkedSequence_ideal u j).symm
          (rfl : MaxContactReduction.iteratedStrictTransform u H j = MaxContactReduction.iteratedStrictTransform u H j)
          (ih (le_of_lt hjl) instj)
        have hstep := @MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ hstar S hv hord u.toMarkedSequenceOfBlowups
          j hlt instsj instsj1 (MaxContactReduction.iteratedStrictTransform u H j) hadm
        have hHeq : Blowup.strictTransform (u.toMarkedSequenceOfBlowups.transitionMapSucc j) (u.toMarkedSequenceOfBlowups.center j)
            (MaxContactReduction.iteratedStrictTransform u H j) = MaxContactReduction.iteratedStrictTransform u H (j + 1) := by
          simp only [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center,
            MaxContactReduction.iteratedStrictTransform_succ]
          rfl
        exact isMaxContactHypersurface_congr S.base instsj1 inst
          (MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec u (j + 1))
          (MarkedBlowupSequenceData.toMarkedSequence_ideal u (j + 1)) hHeq hstep
  exact key t ht (hlft t ht)

private theorem radical_le_of_isReduced_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    (hred : AlgebraicGeometry.IsReduced I.subscheme) : I.radical ≤ I := by
  have := hred
  have hker : Scheme.Hom.ker I.subschemeι = I := Scheme.IdealSheafData.ker_subschemeι I
  have hmem : I ≤ Scheme.IdealSheafData.ofIdeals
      (fun U : X.affineOpens =>
        RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app I.subschemeι U.1))) :=
    le_of_eq hker.symm
  have hle := Scheme.IdealSheafData.le_ofIdeals_iff.mp hmem
  have hgoal : I.radical ≤ Scheme.IdealSheafData.ofIdeals
      (fun U : X.affineOpens =>
        RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app I.subschemeι U.1))) := by
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
    intro U
    rw [Scheme.IdealSheafData.radical_ideal]
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hR := AlgebraicGeometry.IsReduced.component_reduced
      (X := I.subscheme) (I.subschemeι ⁻¹ᵁ U.1)
    refine RingHom.mem_ker.mpr (hR.eq_zero _ ⟨n, ?_⟩)
    rw [← map_pow]
    exact RingHom.mem_ker.mp (hle U hn)
  exact le_trans hgoal (le_of_eq hker)

theorem inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (H : S.scheme.IdealSheafData)
    (hH : @IsMaxContactHypersurface S.base _ S.scheme S.structMap hv.locallyOfFiniteType
      S.ideal S.mult H)
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (h0 : InStrictNormalCrossingPosition (u.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform u H 0])
    (t : ℕ) (ht : t ≤ u.length) :
    InStrictNormalCrossingPosition (u.proj t ≫ S.structMap)
      (MaxContactReduction.iteratedStrictTransform u H t :: (u.boundary t).drop S.boundary.length) := by
  have hsmooth : ∀ i : ℕ, i ≤ u.length →
      AlgebraicGeometry.Smooth (u.proj i ≫ S.structMap) := by
    intro i hi
    have hsm : AlgebraicGeometry.Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec i) :=
      MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups i
        (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hi)
    rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec] at hsm
  have hkey : ∀ i : ℕ, i < u.length →
      MaxContactReduction.iteratedStrictTransform u H i ≤ u.center i := by
    intro i hi
    have hsmi : AlgebraicGeometry.Smooth (u.proj i ≫ S.structMap) := hsmooth i (le_of_lt hi)
    have hlfti : AlgebraicGeometry.LocallyOfFiniteType (u.proj i ≫ S.structMap) :=
      locallyOfFiniteType_of_smooth_morphism hsmi
    have hcz : CharZero S.base := hv.charZero
    have hadm := isMaxContactHypersurface_iteratedStrictTransform hstar S hv hord H hH u i (le_of_lt hi)
    have hcos := hadm.orderAtLeastLocus_subset_support hv.one_le_mult
    have hsupp : (((u.center i).support : Set ↥(u.obj i))) ⊆
        (((MaxContactReduction.iteratedStrictTransform u H i).support : Set ↥(u.obj i))) :=
      Set.Subset.trans (u.center_order i hi) hcos
    have hsupp' : (u.center i).support ≤ (MaxContactReduction.iteratedStrictTransform u H i).support :=
      SetLike.coe_subset_coe.mp hsupp
    have h1 : MaxContactReduction.iteratedStrictTransform u H i ≤
        Scheme.IdealSheafData.vanishingIdeal (u.center i).support :=
      (Scheme.IdealSheafData.gc _ _).mp hsupp'
    rw [Scheme.IdealSheafData.vanishingIdeal_support] at h1
    have hsmZ : AlgebraicGeometry.Smooth
        ((u.center i).subschemeι ≫ (u.proj i ≫ S.structMap)) := u.center_smooth i hi
    have hred : AlgebraicGeometry.IsReduced (u.center i).subscheme :=
      isReduced_of_smooth ((u.center i).subschemeι ≫ (u.proj i ≫ S.structMap))
    exact le_trans h1 (radical_le_of_isReduced_subscheme (u.center i) hred)
  revert ht
  induction t with
  | zero =>
      intro _
      have hb : (u.boundary 0).drop S.boundary.length = [] := by
        rw [u.boundary_zero]
        simp
      rwa [hb]
  | succ j ih =>
      intro hj
      have hjl : j < u.length := hj
      have hjle : j ≤ u.length := le_of_lt hjl
      have hsmj : AlgebraicGeometry.Smooth (u.proj j ≫ S.structMap) := hsmooth j hjle
      have hlj : AlgebraicGeometry.LocallyOfFiniteType (u.proj j ≫ S.structMap) :=
        locallyOfFiniteType_of_smooth_morphism hsmj
      have hnoeth : AlgebraicGeometry.IsNoetherian (u.obj (j + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups (j + 1)
          (by rw [MarkedBlowupSequenceData.toMarkedSequence_length]; exact hj)
      have hnsp : TopologicalSpace.NoetherianSpace ↥(u.obj (j + 1)) := inferInstance
      have hsncj : InStrictNormalCrossingPosition (u.proj j ≫ S.structMap)
          (MaxContactReduction.iteratedStrictTransform u H j :: (u.boundary j).drop S.boundary.length) := ih hjle
      have hZN : HasStrictNormalCrossingsWith (u.proj j ≫ S.structMap) (u.center j)
          ((u.boundary j).drop S.boundary.length) := by
        have hfull := u.center_snc j hjl
        rw [← List.take_append_drop S.boundary.length (u.boundary j)] at hfull
        exact HasStrictNormalCrossingsWith.of_append hfull
      have hcons : HasStrictNormalCrossingsWith (u.proj j ≫ S.structMap) (u.center j)
          (MaxContactReduction.iteratedStrictTransform u H j :: (u.boundary j).drop S.boundary.length) := by
        have hsm' : AlgebraicGeometry.Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec j) := by
          rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
        have hlt : j < u.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
          rwa [MarkedBlowupSequenceData.toMarkedSequence_length]
        have hsnc' : InStrictNormalCrossingPosition (u.toMarkedSequenceOfBlowups.projectionToSpec j)
            (MaxContactReduction.iteratedStrictTransform u H j :: (u.boundary j).drop S.boundary.length) := by
          rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec]
        have hZN' : HasStrictNormalCrossingsWith (u.toMarkedSequenceOfBlowups.projectionToSpec j) (u.toMarkedSequenceOfBlowups.center j)
            ((u.boundary j).drop S.boundary.length) := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_center]
          exact hZN
        have hHZ' : MaxContactReduction.iteratedStrictTransform u H j ≤ u.toMarkedSequenceOfBlowups.center j := by
          rw [MarkedBlowupSequenceData.toMarkedSequence_center]
          exact hkey j hjl
        have hres := @MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center hstar S u.toMarkedSequenceOfBlowups j hlt hsm'
          (MaxContactReduction.iteratedStrictTransform u H j) ((u.boundary j).drop S.boundary.length)
          hsnc' hZN' hHZ'
        rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_center] at hres
        exact hres
      have hbd : (u.boundary (j + 1)).drop S.boundary.length =
          ((u.boundary j).drop S.boundary.length).map
              (Blowup.strictTransform (u.map j) (u.center j)) ++
            [Blowup.exceptionalIdeal (u.map j) (u.center j)] :=
        u.boundary_succ_drop hjl S.boundary.length
          (by rw [u.boundary_length j hjle]; omega)
      rw [hbd, MaxContactReduction.iteratedStrictTransform_succ, u.proj_succ j, Category.assoc]
      exact inStrictNormalCrossingPosition_strictTransform_cons_append (u.proj j ≫ S.structMap) (u.map j)
        (u.center j) (MaxContactReduction.iteratedStrictTransform u H j)
        ((u.boundary j).drop S.boundary.length) (u.isBlowup j hjl) hsncj hcons

end FunctorialResolution.EmbeddedResolution

end
