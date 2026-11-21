import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContractsOfConstant

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

structure Var (F : Type) [Field F] : Type where

  N : ℕ

  I : (PSpace F N).IdealSheafData

  dim : ℕ

  smooth : SmoothOfRelativeDimension dim (I.subschemeι ≫ PSpace.str F N)

  geomIntegral : GeometricallyIntegral (I.subschemeι ≫ PSpace.str F N)

namespace Var

variable {F : Type} [Field F] (Y : Var F)

def X : Scheme.{0} := Y.I.subscheme

def ι : Y.X ⟶ PSpace F Y.N := Y.I.subschemeι

def str : Y.X ⟶ Sp F := Y.ι ≫ PSpace.str F Y.N

theorem ι_str : Y.ι ≫ PSpace.str F Y.N = Y.str := rfl

instance isClosedImmersion_ι : IsClosedImmersion Y.ι :=
  inferInstanceAs (IsClosedImmersion Y.I.subschemeι)

instance smooth_str : SmoothOfRelativeDimension Y.dim Y.str := Y.smooth

instance geometricallyIntegral_str : GeometricallyIntegral Y.str := Y.geomIntegral

instance geometricallyConnected_str : GeometricallyConnected Y.str :=
  ⟨fun _ _ y _ fst snd h =>
    have := GeometricallyIntegral.geometrically_isIntegral (f := Y.str) y fst snd h
    inferInstance⟩

instance isIntegral_X : IsIntegral Y.X := GeometricallyIntegral.isIntegral_of_subsingleton Y.str

theorem isProjOver : IsProjOver Y.str := ⟨Y.N, Y.ι, inferInstance, rfl⟩

instance isProper_str : IsProper Y.str :=
  have := Geo.Tor.isProper_str F Y.N
  inferInstanceAs (IsProper (Y.ι ≫ PSpace.str F Y.N))

theorem isNormalScheme : IsNormalScheme Y.X :=
  have := SmoothOfRelativeDimension.smooth Y.dim Y.str
  isNormalScheme_of_smooth Y.str

theorem topologicalKrullDim_eq : topologicalKrullDim Y.X = Y.dim := by
  have hc (U : Y.X.Opens) (hU : IsAffineOpen U) (h : (U : Set Y.X).Nonempty) :
      topologicalKrullDim (U : Set Y.X) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y.X, U))).trans
      (SmoothDim.ringKrullDim_affineOpen F _ Y.str _ inferInstance U hU h)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens (Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens
      (Opens.mem_top (genericPoint Y.X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

attribute [local instance] MvPolynomial.gradedAlgebra in

def coneIdeal : Ideal (MvPolynomial (Fin (Y.N + 1)) F) :=
  (show ProjectiveSpectrum (ProjSpace.grading F Y.N) from
    Y.ι (genericPoint Y.X)).asHomogeneousIdeal.toIdeal

section OfImmersion

variable {Z : Scheme.{0}} {N : ℕ} (i : Z ⟶ PSpace F N) [IsClosedImmersion i] (d : ℕ)
  [SmoothOfRelativeDimension d (i ≫ PSpace.str F N)] [GeometricallyIntegral (i ≫ PSpace.str F N)]

omit [SmoothOfRelativeDimension d (i ≫ PSpace.str F N)]
  [GeometricallyIntegral (i ≫ PSpace.str F N)] in

theorem subschemeι_ker : i.ker.subschemeι = inv i.toImage ≫ i := by
  rw [IsIso.eq_inv_comp]; exact i.toImage_imageι

def ofClosedImmersion : Var F where
  N := N
  I := i.ker
  dim := d
  smooth := by
    rw [subschemeι_ker, Category.assoc]
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} d
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩) ‹_›
  geomIntegral := by
    rw [subschemeι_ker, Category.assoc]
    exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩) ‹_›

def isoOfClosedImmersion : Z ≅ (ofClosedImmersion i d).X :=
  show Z ≅ i.image from asIso i.toImage

theorem isoOfClosedImmersion_ι :
    (isoOfClosedImmersion i d).hom ≫ (ofClosedImmersion i d).ι = i := i.toImage_imageι

end OfImmersion

theorem exists_iso {Z : Scheme.{0}} (p : Z ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p]
    [GeometricallyConnected p] (h : IsProjOver p) :
    ∃ (Y : Var F) (e : Z ≅ Y.X), Y.dim = d ∧ e.hom ≫ Y.str = p := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := SmoothOfRelativeDimension.smooth d (i ≫ PSpace.str F N)
  have := geometricallyIntegral_of_smooth (i ≫ PSpace.str F N)
  exact ⟨ofClosedImmersion i d, isoOfClosedImmersion i d, rfl,
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (isoOfClosedImmersion_ι i d))⟩

instance algebraΓ : Algebra F Γ(Y.X, ⊤) := algebraΓOfHom Y.str

theorem algebraMap_Γ (a : F) :
    algebraMap F Γ(Y.X, ⊤) a = Y.str.appTop ((Scheme.ΓSpecIso (.of F)).inv a) := rfl

abbrev Fn : Type := Y.X.functionField

instance algebraFn : Algebra F Y.Fn := (Cartier.constFn Y.str).toAlgebra

theorem algebraMap_Fn : algebraMap F Y.Fn = Cartier.constFn Y.str := rfl

instance isScalarTower_Fn : IsScalarTower F Γ(Y.X, ⊤) Y.Fn :=
  .of_algebraMap_eq fun a => congrArg (fnOf ⊤ trivial) (LB.resG_self (X := Y.X) le_top _)

theorem regAt_algebraMap (x : Y.X) (a : F) : RegAt x (algebraMap F Y.Fn a) :=
  regAt_fnOf (U := ⊤) trivial trivial _

abbrev Dv : Type := CartierDiv Y.X

def Eff (Δ : Y.Dv) : Prop := Δ.Eff

def H0 (Δ : Y.Dv) : Submodule F Y.Fn := Δ.sections.restrictScalars F

variable {Y} in

theorem mem_riemannRochSpace_iff_regularAt_everywhere {Δ : Y.Dv} {f : Y.Fn} : f ∈ Y.H0 Δ ↔ ∀ x, Δ.RegularAt x f := mem_sections

variable {Y} in

theorem eff_iff_one_mem {Δ : Y.Dv} : Y.Eff Δ ↔ (1 : Y.Fn) ∈ Y.H0 Δ := mem_riemannRochSpace_iff_regularAt_everywhere.symm

theorem eff_zero : Y.Eff 0 := CartierDiv.eff_zero

theorem eff_add (a b : Y.Dv) (ha : Y.Eff a) (hb : Y.Eff b) : Y.Eff (a + b) :=
  CartierDiv.Eff.add ha hb

theorem mul_mem_riemannRochSpace_add (Δ Δ' : Y.Dv) (f g : Y.Fn) (hf : f ∈ Y.H0 Δ) (hg : g ∈ Y.H0 Δ') :
    f * g ∈ Y.H0 (Δ + Δ') := mem_riemannRochSpace_iff_regularAt_everywhere.2 fun x => (mem_riemannRochSpace_iff_regularAt_everywhere.1 hf x).mul (mem_riemannRochSpace_iff_regularAt_everywhere.1 hg x)

theorem riemannRoch_mono (Δ Δ' : Y.Dv) (h : Y.Eff (Δ' - Δ)) : Y.H0 Δ ≤ Y.H0 Δ' := fun f hf => by
  simpa using Y.mul_mem_riemannRochSpace_add Δ (Δ' - Δ) f 1 hf (eff_iff_one_mem.1 h)

abbrev lb (Δ : Y.Dv) : LB Y.X := toLB Δ

variable {Y} in

def cohEquiv {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (h : Presents Δ L r) :
    coh (twist (structureModule Y.X) L) 0 ≃ₗ[F] Y.H0 Δ :=
  ((cohZeroTwistEquiv L).trans h.secEquiv).restrictScalars F

instance finiteDimensional_riemannRochSpace (Δ : Y.Dv) : FiniteDimensional F (Y.H0 Δ) :=
  have := finite_coh_zero_twist_of_isProjOver Y.algebraMap_Γ Y.isProjOver (isLB_toLB Δ)
  .equiv (cohEquiv (presents_toLB Δ))

def KY : Y.Dv := canonical Y.str Y.dim

abbrev Cl : Type := Closeds Y.X

def properCl (Z : Y.Cl) : Prop := Z ≠ ⊤

def subCl (Z Z' : Y.Cl) : Prop := Z ≤ Z'

def supp (Δ : Y.Dv) : Y.Cl := Δ.supp

def bpf (Δ : Y.Dv) (V : Set Y.Fn) : Prop := Δ.BasePointFree V

def vanishOn (Δ : Y.Dv) (f : Y.Fn) (Z : Y.Cl) : Prop := Δ.VanishesOn f Z

def phiBir (Δ : Y.Dv) (V : Set Y.Fn) : Prop := Δ.Birational F V

def phiNoContr (Δ : Y.Dv) (V : Set Y.Fn) (bd : Y.Cl) : Prop := Δ.NoContract F V bd

theorem isCompleteCurve_iff (Z : Y.Cl) : IsCompleteCurve F Z ↔
    IsIrreducible (Z : Set Y.X) ∧ topologicalKrullDim (Z : Set Y.X) = 1 :=
  GlobalTheory.isCompleteCurve_iff Y.algebraMap_Γ

abbrev sysOf {L : LB Y.X} (hL : L.IsLB) {n : ℕ} (s : Fin n → L.Sec) : LinSys F where
  Y := Y.X
  str := Y.str
  D := Y.dim
  L := L
  isLB := hL
  N := n
  b := s

variable {Y} in

def sec {Δ : Y.Dv} (f : Y.H0 Δ) : (Y.lb Δ).Sec := (presents_toLB Δ).secEquiv.symm ⟨f.1, f.2⟩

variable {Y} in

@[simp] theorem rat_sec {Δ : Y.Dv} (f : Y.H0 Δ) : (presents_toLB Δ).rat (sec f) = f :=
  congrArg Subtype.val ((presents_toLB Δ).secEquiv.apply_symm_apply ⟨f.1, f.2⟩)

section LinSys

variable {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ)

abbrev linSys : LinSys F := Y.sysOf (isLB_toLB Δ) fun j => sec (b j)

end LinSys

section Hyperplane

open ProjSpace

abbrev O1 : LB Y.X := (ProjSpace.O1 F Y.N).pull Y.ι

theorem isLineBundle_twistingSheafOne : Y.O1.IsLB := LB.isLB_pull (O1_isLB F Y.N) _

theorem isAmple_projective_O_one : IsAmpleLB Y.O1 :=
  (GlobalTheory.isAmple_projective_O_one F Y.N).pull_of_isClosedImmersion _

def idx (i : Fin (Y.N + 1)) : Y.O1.ι := fun _ => i

theorem twistingSheafOne_chart_eq_preimage_standardChart (i : Fin (Y.N + 1)) : Y.O1.U (Y.idx i) = Y.ι ⁻¹ᵁ chart F Y.N i :=
  LB.pull_U (L := ProjSpace.O1 F Y.N) Y.ι (Y.idx i)

variable {i : Fin (Y.N + 1)} (hi : Y.ι (genericPoint Y.X) ∈ chart F Y.N i)

include hi in

theorem genericPoint_mem_twistingSheafOne_chart : genericPoint Y.X ∈ Y.O1.U (Y.idx i) := (Y.twistingSheafOne_chart_eq_preimage_standardChart i).ge hi

def hyp : Y.Dv := ofLB Y.isLineBundle_twistingSheafOne (Y.idx i) (Y.genericPoint_mem_twistingSheafOne_chart hi)

theorem presents_hyp : Presents (Y.hyp hi) Y.O1 (frameRat _ (Y.idx i) (Y.genericPoint_mem_twistingSheafOne_chart hi)) :=
  presents_ofLB _ _ _

end Hyperplane

end Var

def RiemannRochFinite (F : Type) [Field F] : Prop :=
  ∀ (Y : Var F) (Δ : Y.Dv), FiniteDimensional F (Y.H0 Δ)

theorem riemannRoch_finite (F : Type) [Field F] : RiemannRochFinite F := Var.finiteDimensional_riemannRochSpace

section Proj

open ProjSpace

variable (F : Type) [Field F] (n : ℕ)

instance smooth_id_str : SmoothOfRelativeDimension n (𝟙 _ ≫ PSpace.str F n) := by
  rw [Category.id_comp]; exact smoothOfRelativeDimension_pspace F n

instance geometricallyIntegral_id_str : GeometricallyIntegral (𝟙 _ ≫ PSpace.str F n) := by
  have := SmoothOfRelativeDimension.smooth n (𝟙 _ ≫ PSpace.str F n)
  have : GeometricallyConnected (𝟙 _ ≫ PSpace.str F n) := by
    rw [Category.id_comp]; exact geometricallyConnected_pspace F n
  exact geometricallyIntegral_of_smooth _

def proj : Var F := Var.ofClosedImmersion (𝟙 (PSpace F n)) n

instance : Inhabited (Var F) := ⟨proj F 0⟩

theorem proj_dim : (proj F n).dim = n := rfl

instance isIso_proj_ι : IsIso (proj F n).ι :=
  have : IsIso ((Var.isoOfClosedImmersion (𝟙 (PSpace F n)) n).hom ≫ (proj F n).ι) :=
    (Var.isoOfClosedImmersion_ι (𝟙 (PSpace F n)) n).symm ▸ inferInstanceAs (IsIso (𝟙 _))
  IsIso.of_isIso_comp_left (Var.isoOfClosedImmersion (𝟙 (PSpace F n)) n).hom _

end Proj

end GlobalTheory.ProjVar
