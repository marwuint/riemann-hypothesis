import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.GtBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.Bdy

section Algebra

theorem exists_etale_local (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (k₀ k : Type) [Field k₀] [Field k]
    [Algebra k₀ k] [FiniteDimensional k₀ k] [Algebra.IsSeparable k₀ k] (φ : k₀ →+* ResidueField V) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (_ : IsLocalHom (algebraMap V W))
      (j : k →+* ResidueField W), Module.Finite V W ∧ Algebra.Etale V W ∧
      j.comp (algebraMap k₀ k) = (ResidueField.map (algebraMap V W)).comp φ := by
  let pb := Field.powerBasisOfFiniteOfSeparable k₀ k
  have hm := minpoly.monic pb.isIntegral_gen
  have hs : ((minpoly k₀ pb.gen).map φ).Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k₀ pb.gen)
  obtain ⟨g, hgm, hg, hdvd⟩ := Polynomial.exists_monic_irreducible_factor ((minpoly k₀ pb.gen).map φ) (fun h => by
    have := Polynomial.degree_eq_zero_of_isUnit h
    rw [Polynomial.degree_map] at this
    exact (minpoly.degree_pos pb.isIntegral_gen).ne' this)
  obtain ⟨f, rfl, -, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := residue V)
    (Polynomial.mem_lifts_of_surjective residue_surjective g) hgm
  have hfin : Module.Finite V (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hf).basis
  have hfree : Module.Free V (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Fact (Irreducible (f.map (residue V))) := ⟨hg⟩
  have hmax : ((maximalIdeal V).map (algebraMap V (AdjoinRoot f))).IsMaximal := by
    rw [AdjoinRoot.algebraMap_eq]
    exact Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField (AdjoinRoot (f.map (residue V))))
      (AdjoinRoot.quotEquivQuotMap f (maximalIdeal V)).toRingEquiv.toMulEquiv)
  have hl : IsLocalRing (AdjoinRoot f) := by
    refine IsLocalRing.of_unique_max_ideal ⟨_, hmax, fun M hM => ?_⟩
    have hc : (M.comap (algebraMap V (AdjoinRoot f))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact (hmax.eq_of_le hM.ne_top (Ideal.map_le_iff_le_comap.2 (IsLocalRing.eq_maximalIdeal hc).ge)).symm
  have hme : (maximalIdeal V).map (algebraMap V (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal hmax
  have hlh : IsLocalHom (algebraMap V (AdjoinRoot f)) := ((IsLocalRing.local_hom_TFAE _).out 0 2).2 hme.le
  have hres : (algebraMap (ResidueField V) (ResidueField (AdjoinRoot f))).comp (residue V) =
      (residue _).comp (algebraMap V (AdjoinRoot f)) := RingHom.ext fun a => ResidueField.map_residue _ a
  have hroot : aeval (residue _ (AdjoinRoot.root f)) (f.map (residue V)) = 0 := by
    rw [aeval_def, eval₂_map, hres, ← hom_eval₂, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, map_zero]
  have hsep : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot f)) := by
    have hα : IsSeparable (ResidueField V) (residue _ (AdjoinRoot.root f)) :=
      (hs.of_dvd hdvd).of_dvd (minpoly.dvd _ _ hroot)
    have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hα
    refine ⟨fun y => IntermediateField.isSeparable_of_mem_isSeparable (ResidueField V) _
      (L := IntermediateField.adjoin (ResidueField V) {residue _ (AdjoinRoot.root f)}) ?_⟩
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    have e : residue _ (AdjoinRoot.mk f q) = aeval (residue _ (AdjoinRoot.root f)) (q.map (residue V)) := by
      rw [aeval_def, eval₂_map, hres, ← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq]
    rw [e]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
  have hun : Algebra.FormallyUnramified V (AdjoinRoot f) := Algebra.FormallyUnramified.of_map_maximalIdeal hme
  have hfp : Algebra.FinitePresentation V (AdjoinRoot f) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  letI : Algebra k₀ (ResidueField (AdjoinRoot f)) := ((ResidueField.map (algebraMap V (AdjoinRoot f))).comp φ).toAlgebra
  have hr : aeval (residue _ (AdjoinRoot.root f)) (minpoly k₀ pb.gen) = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    have : aeval (residue _ (AdjoinRoot.root f)) ((minpoly k₀ pb.gen).map φ) = 0 := by rw [hc, map_mul, hroot, zero_mul]
    rw [aeval_def, eval₂_map] at this
    exact this
  exact ⟨AdjoinRoot f, _, hl, _, hlh, (pb.lift _ hr).toRingHom, hfin, Algebra.Etale.of_formallyUnramified_of_flat,
    (pb.lift _ hr).comp_algebraMap⟩

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev Cpl (X : Scheme.{0}) (x : X) : Type := AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

structure BDat {X : Scheme.{0}} (t₀ : SAB H X) (x : X) : Type 1 where
  R : Type
  [ring : CommRing R]
  [dom : IsDomain R]
  [loc : IsLocalRing R]
  [ch0 : CharZero R]
  [noeth : IsNoetherianRing R]
  [normal : IsIntegrallyClosed R]
  [complete : IsAdicComplete (maximalIdeal R) R]
  [alg : Algebra (Cpl X x) R]
  fin : Module.Finite (Cpl X x) R
  etale : Algebra.Etale (Cpl X x) R
  locHom : IsLocalHom (algebraMap (Cpl X x) R)
  t : SAB H (Sp R)
  m : SABMap t t₀ (spMap (algebraMap (Cpl X x) R) ≫ fromSpecCompletedStalk X x)
  U : PELUnif (maximalIdeal R) t
  unitOn : ∀ y, PsiUnitOn U.D.toPre y (abLocus t.G)
  tors : U.TorsionIso

attribute [instance] BDat.ring BDat.dom BDat.loc BDat.ch0 BDat.noeth BDat.normal BDat.complete BDat.alg

theorem split_pull {S : Scheme.{0}} {t₀ : SAB H S} {k : Type} [Field k] (q : Sp k ⟶ S) {S' : SplitExt (Sp k)}
    (hS : S'.IsGt ((Over.pullback q).obj t₀.G)) {R : Type} [CommRing R] [IsLocalRing R] (j : k →+* ResidueField R)
    {ι : Sp R ⟶ S} (hq : spMap j ≫ q = spMap (residue R) ≫ ι) {t : SAB H (Sp R)} (m : SABMap t t₀ ι) :
    ∃ S₁ : SplitExt (Sp (ResidueField R)), S₁.IsGt ((Over.pullback (spMap (residue R))).obj t.G) := by
  obtain ⟨S₁, -, -, -, -, hS₁⟩ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gtBaseChange _ _ (spMap j) S' _ hS
  have gp₁ := ((isGrpPullback_pullback _ (spMap j)).comp (isGrpPullback_pullback t₀.G _)).congr hq rfl
  have gp₂ := (isGrpPullback_pullback t.G (spMap (residue R))).comp m.cart
  obtain ⟨e, he, -⟩ := grpPullback_iso gp₁ gp₂
  exact ⟨S₁, isGt_of_iso e hS₁⟩

theorem residue_comp {X : Scheme.{0}} (x : X) [IsNoetherianRing (X.presheaf.stalk x)] {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra (Cpl X x) R] [IsLocalHom (algebraMap (Cpl X x) R)] :
    spMap ((ResidueField.map (algebraMap (Cpl X x) R)).comp
      (ResidueField.map (algebraMap (X.presheaf.stalk x) (Cpl X x)))) ≫ X.fromSpecResidueField x =
      spMap (residue R) ≫ spMap (algebraMap (Cpl X x) R) ≫ fromSpecCompletedStalk X x := by
  have h : ((ResidueField.map (algebraMap (Cpl X x) R)).comp
      (ResidueField.map (algebraMap (X.presheaf.stalk x) (Cpl X x)))).comp (residue (X.presheaf.stalk x)) =
      (residue R).comp ((algebraMap (Cpl X x) R).comp (algebraMap (X.presheaf.stalk x) (Cpl X x))) := rfl
  have h' := (spMap_comp _ _).symm.trans ((congrArg spMap h).trans ((spMap_comp _ _).trans
    (congrArg (spMap (residue R) ≫ ·) (spMap_comp _ _))))
  have h'' := congrArg (· ≫ X.fromSpecStalk x) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (by simp only [Category.assoc]; rfl))

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

theorem generic_image {X : Scheme.{0}} (x : X) {R : Type} [CommRing R] [IsDomain R] (φ : X.presheaf.stalk x →+* R)
    (hφ : Function.Injective φ) (ξ : Sp R) (hξ : ξ.asIdeal = ⊥) (y : X) (hy : y ⤳ (spMap φ ≫ X.fromSpecStalk x) ξ) :
    y = (spMap φ ≫ X.fromSpecStalk x) ξ := by
  rw [Scheme.Hom.comp_apply] at hy ⊢
  have h₁ : X.fromSpecStalk x (spMap φ ξ) ⤳ x := by
    have : X.fromSpecStalk x (spMap φ ξ) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  obtain ⟨q, rfl⟩ : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy.trans h₁
  have h₂ := (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.1 hy
  congr 1
  have h₃ := (PrimeSpectrum.le_iff_specializes _ _).2 h₂
  refine PrimeSpectrum.ext (le_antisymm h₃ fun a ha => ?_)
  have : φ a = 0 := by
    have h : φ a ∈ ξ.asIdeal := ha
    rwa [hξ] at h
  rw [hφ (this.trans (map_zero φ).symm)]
  exact q.asIdeal.zero_mem

end GlobalTheory.LocM.Bdy
