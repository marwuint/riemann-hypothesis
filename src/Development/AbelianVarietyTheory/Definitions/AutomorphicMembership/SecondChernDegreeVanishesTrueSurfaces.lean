import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegOfRankPullbackIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Limits (pullback)
open GlobalTheory.VB Formalism.BasicNotions
open GlobalTheory.LieVB (omega omegaBase)
open GlobalTheory.Vert (SmallPic smallPicEquiv)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol IsProjSurface degCh2)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ShFam.Pad

structure ProjCode (R : Type) [CommRing R] : Type where

  n : ℕ

  I : (PSpace R n).IdealSheafData

namespace ProjCode

variable {R : Type} [CommRing R] (C : ProjCode R)

def X : Scheme.{0} := C.I.subscheme

def str : C.X ⟶ Sp R := C.I.subschemeι ≫ PSpace.str R C.n

theorem isProjOver : IsProjOver C.str :=
  ⟨C.n, C.I.subschemeι, inferInstanceAs (IsClosedImmersion C.I.subschemeι), rfl⟩

instance algebra : Algebra R Γ(C.X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ C.str.appTop).hom.toAlgebra

theorem strHom_eq {k : Type} [Field k] (C : ProjCode k) : strHom k C.X = C.str :=
  GlobalTheory.strHom_eq fun _ => rfl

theorem exists_iso {Y : Scheme.{0}} {f : Y ⟶ Sp R} (h : IsProjOver f) :
    ∃ (C : ProjCode R) (e : C.X ≅ Y), e.hom ≫ f = C.str := by
  obtain ⟨n, i, _, hi⟩ := h
  have hk : i.ker.subschemeι.ker = i.ker := Scheme.IdealSheafData.ker_subschemeι _
  have := IsClosedImmersion.isIso_lift _ _ hk
  let e := asIso (IsClosedImmersion.lift _ i hk.le)
  have he : e.hom ≫ i.ker.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  refine ⟨⟨n, i.ker⟩, e.symm, ?_⟩
  change e.inv ≫ f = i.ker.subschemeι ≫ PSpace.str R n
  rw [Iso.inv_comp_eq, reassoc_of% he, hi]

end ProjCode

abbrev toSpZ (Y : Scheme.{0}) : Y ⟶ Sp ℤ := specZIsTerminal.from Y

theorem isProjOver_toSpZ {R : Type} [CommRing R] [Module.Finite ℤ R] {Y : Scheme.{0}}
    {f : Y ⟶ Sp R} (h : IsProjOver f) : IsProjOver (toSpZ Y) := by
  obtain ⟨N, i, hi, -⟩ := h
  have hb : IsFinite (spMap (Int.castRingHom R)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := R)).2 inferInstance
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom R)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom R)) :=
    MorphismProperty.of_isPullback P.flip hb
  have := isProjOver_comp_of_finite ℤ (PSpace ℤ N) Y
    (i ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom R)) (PSpace.str ℤ N) inferInstance
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exact specZIsTerminal.hom_ext _ (toSpZ Y) ▸ this

theorem isArithVar_toSpZ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsArithVar (toSpZ Y) D :=
  have := h.finite
  ⟨inferInstance, inferInstance, h.isIntegral, isProjOver_toSpZ h.isProjOver,
    specZIsTerminal.hom_ext (p ≫ spMap (Int.castRingHom k))
      (toSpZ Y ≫ spMap (Int.castRingHom ℤ)) ▸ h.flat, h.dim_eq⟩

structure PPCode (S : Scheme.{0}) : Type where

  C : ProjCode ℤ

  π : C.X ⟶ S

  [grp : GrpObj (Over.mk π)]

  isAb : IsAbelianScheme (Over.mk π)

  g : ℕ

  pos : 1 ≤ g

  smoothDim : SmoothOfRelativeDimension g π

  c : SmallPic (Over.mk π ⊗ Over.mk π).left

  isPol : IsPrincipalPol (Over.mk π) (smallPicEquiv _ c)

namespace PPCode

variable {S S' : Scheme.{0}}

def P (Q : PPCode S) : PPAS S :=
  letI := Q.grp
  { A := Over.mk Q.π, isAb := Q.isAb, g := Q.g, smoothDim := Q.smoothDim,
    c := smallPicEquiv _ Q.c, isPol := Q.isPol }

@[simp] theorem P_g (Q : PPCode S) : Q.P.g = Q.g := rfl

theorem isProjOver (Q : PPCode S) : IsProjOver (toSpZ Q.P.A.left) :=
  (specZIsTerminal.hom_ext Q.C.str (toSpZ Q.C.X) ▸ Q.C.isProjOver : IsProjOver (toSpZ Q.C.X))

theorem exists_isPull (P : PPAS S) (hg : 1 ≤ P.g) (f : S' ⟶ S)
    (h : IsProjOver (toSpZ (pullback P.A.hom f))) :
    ∃ (Q : PPCode S') (φ : Q.P.A.left ⟶ P.A.left), Q.g = P.g ∧ Q.P.IsPull P f φ := by
  obtain ⟨C, e, -⟩ := ProjCode.exists_iso h
  let B := (Over.pullback f).obj P.A
  let ε : B ≅ Over.mk (e.hom ≫ pullback.snd P.A.hom f) :=
    Over.isoMk e.symm (e.inv_hom_id_assoc _)
  letI := GrpObj.ofIso ε
  have : IsMonHom ε.hom := isMonHom_ofIso ε
  have : IsMonHom ε.symm.hom := inferInstanceAs (IsMonHom ε.inv)
  have H := ((isGrpPullback_of_iso ε.symm).comp (isGrpPullback_pullback P.A f)).congr
    (Category.id_comp f) rfl
  refine ⟨⟨C, _, PolPull.isAbelianScheme_of_isGrpPullback P.isAb H, P.g, hg,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback H.1 P.smoothDim,
    (smallPicEquiv _).symm (CechPic.pull (sqMap H.1.w) P.c), ?_⟩, _, rfl, H, ?_⟩
  · rw [AddEquiv.apply_symm_apply]
    exact PPAS.isPrincipalPol_pull H P.isPol
  · exact AddEquiv.apply_symm_apply _ _

theorem exists_isPull_of_isIso (P : PPAS S) (hg : 1 ≤ P.g) (f : S' ⟶ S) [IsIso f]
    (h : IsProjOver (toSpZ P.A.left)) :
    ∃ (Q : PPCode S') (φ : Q.P.A.left ⟶ P.A.left), Q.g = P.g ∧ Q.P.IsPull P f φ :=
  exists_isPull P hg f (isProjOver_toSpZ
    (isProjOver_comp_of_finite ℤ _ _ (pullback.fst P.A.hom f) _ inferInstance h))

theorem exists_const {R : Type} [CommRing R] [Module.Finite ℤ R] (P : Out.PolAV (Sp R))
    (hg : 1 ≤ P.g) {f : S' ⟶ Sp R} (hf : IsProjOver f) :
    ∃ (Q : PPCode S') (φ : Q.P.A.left ⟶ P.A.left), Q.g = P.g ∧ Q.P.IsPull (.ofPolAV P) f φ :=
  exists_isPull (.ofPolAV P) hg f
    (isProjOver_toSpZ (ProjSpace.isProjOver_pullback (ProjSpace.isProjOver_polAV P) hf))

end PPCode

def omegaPullIso {S S' : Scheme.{0}} {P : PPAS S} {P' : PPAS S'} {f : S' ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} (h : P'.IsPull P f φ) :
    (Scheme.Modules.pullback f).obj (omega P.A) ≅ omega P'.A := asIso (omegaBase h.1)

structure Surf : Type where

  C : ProjCode ℤ

  arith : IsArithVar C.str 1

  A : PPCode C.X

namespace Surf

variable (s : Surf)

instance : IsIntegral s.C.X := s.arith.isIntegral

def ch2 : ℝ := s.A.P.ch2Omega s.C.str

def degOm : ℝ := s.A.P.degOmega s.C.str

end Surf

theorem cxDeg_pullback_iso {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (e : Y ≅ X) (w : e.hom ≫ p = q) (E : X.Modules) (r : ℕ) :
    cxDeg q ((Scheme.Modules.pullback e.hom).obj E) r = cxDeg p E r := by
  subst w
  let ε : cxFibre (e.hom ≫ p) ≅ cxFibre p := @asIso _ _ _ _ (pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _)
    (by simp) (by simp)) (Limits.pullback.map_isIso ..)
  have h₁ : ε.hom ≫ cxFibre.fst p = cxFibre.fst (e.hom ≫ p) ≫ e.hom := pullback.lift_fst _ _ _
  have h₂ : ε.hom ≫ cxFibre.snd p = cxFibre.snd (e.hom ≫ p) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hf (r : ℂ) : ε.hom.appTop (algebraMap ℂ Γ(cxFibre p, ⊤) r) =
      algebraMap ℂ Γ(cxFibre (e.hom ≫ p), ⊤) r := by
    change _ = (cxFibre.snd (e.hom ≫ p)).appTop _
    rw [← h₂, Scheme.Hom.comp_appTop]
    rfl
  rw [cxDeg, cxDeg, ← CxLine.degOfRank_pullback_iso ε hf]
  exact degOfRank_congr ℂ ((Scheme.Modules.pullbackComp _ _).app E ≪≫
    (Scheme.Modules.pullbackCongr h₁.symm).app E ≪≫ ((Scheme.Modules.pullbackComp _ _).app E).symm)

theorem Surf.exists_iso {X : Scheme.{0}} {p : X ⟶ Sp ℤ} (hX : IsArithVar p 1) (P : PPAS X)
    (hg : 1 ≤ P.g) (h : IsProjOver (toSpZ P.A.left)) :
    ∃ (s : Surf) (e : s.C.X ≅ X) (φ : s.A.P.A.left ⟶ P.A.left), e.hom ≫ p = s.C.str ∧
      s.A.g = P.g ∧ s.A.P.IsPull P e.hom φ ∧ s.degOm = P.degOmega p := by
  obtain ⟨C, e, he⟩ := ProjCode.exists_iso hX.isProjOver
  obtain ⟨Q, φ, hQ, H⟩ := PPCode.exists_isPull_of_isIso P hg e.hom h
  have := hX.isIntegral
  have := hX.flat
  refine ⟨⟨C, ⟨inferInstance, inferInstance, .of_isIso e.inv, C.isProjOver, ?_, ?_⟩, Q⟩, e, φ, he,
    hQ, H, congrArg Int.cast ?_⟩
  · rw [← he, Category.assoc]
    infer_instance
  · exact (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).trans hX.dim_eq
  · rw [PPAS.degOmega, PPAS.degOmega, ← cxDeg_congr (omegaPullIso H), cxDeg_pullback_iso e he,
      PPCode.P_g, hQ]

structure SurfFp : Type where

  p : ℕ

  [prime : Fact p.Prime]

  C : ProjCode (ZMod p)

  surf : IsProjSurface (ZMod p) C.X

  A : PPCode C.X

namespace SurfFp

attribute [instance] prime

variable (s : SurfFp)

instance : IsIntegral s.C.X := s.surf.1

def ch2Q : ℚ := degCh2 (ZMod s.p) (omega s.A.P.A) s.A.g

def ch2 : ℝ := s.ch2Q

end SurfFp

structure SurfSt : Type 1 where

  Surf : Type

  surfCh2 : Surf → ℝ

  surfDegOm : Surf → ℝ

  SurfFp : Type

  surfFpCh2 : SurfFp → ℝ

namespace SurfSt

variable {D : D7}

def of (X : DivX D) : SurfSt := ⟨X.Surf, X.surfCh2, X.surfDegOm, X.SurfFp, X.surfFpCh2⟩

def put (t : SurfSt) (X : DivX D) : DivX D :=
  { X with
    Surf := t.Surf
    surfCh2 := t.surfCh2
    surfDegOm := t.surfDegOm
    SurfFp := t.SurfFp
    surfFpCh2 := t.surfFpCh2 }

@[simp] theorem of_put (t : SurfSt) (X : DivX D) : of (t.put X) = t := rfl

@[simp] theorem put_of (X : DivX D) : (of X).put X = X := rfl

end SurfSt

variable {D : D7} {X : DivX D}

theorem Surf.exists_const (F : Type) [Field F] [NumberField F] (W : _root_.WeierstrassCurve (𝓞 F))
    [W.IsElliptic] : ∃ (s : Surf) (e : s.C.X ≅ PSpace (𝓞 F) 1)
      (φ : s.A.P.A.left ⟶ (WeierstrassCurve.ellPolAV W).A.left), s.A.g = 1 ∧
        s.A.P.IsPull (.ofPolAV (WeierstrassCurve.ellPolAV W)) (e.hom ≫ PSpace.str (𝓞 F) 1) φ := by
  have h := ProjModel.isArithVar_pspace (𝓞 F) (ProjModel.ringKrullDim_ringOfIntegers F) 1
  obtain ⟨Q, -⟩ := PPCode.exists_const (WeierstrassCurve.ellPolAV W) le_rfl h.isProjOver
  obtain ⟨s, e, -⟩ := Surf.exists_iso (isArithVar_toSpZ h) Q.P Q.pos Q.isProjOver
  obtain ⟨Q', φ, hg, H⟩ := PPCode.exists_const (WeierstrassCurve.ellPolAV W) le_rfl
    (isProjOver_comp_of_finite _ _ _ e.hom _ inferInstance h.isProjOver)
  exact ⟨⟨s.C, s.arith, Q'⟩, e, φ, hg, H⟩

instance : Fact (∀ r : ℚ, r ^ 2 ≠ 1 + 5 * r) := ⟨fun r h => by
  have e : IsSquare (29 : ℚ) := ⟨2 * r - 5, by linear_combination (-4) * h⟩
  exact absurd (Rat.isSquare_ofNat_iff.1 e) (by decide +kernel)⟩

abbrev QuadraticFieldTwentyNine : Type := QuadraticAlgebra ℚ 1 5

instance : NumberField QuadraticFieldTwentyNine := NumberField.of_module_finite ℚ _

theorem omega_sq_sqrtTwentyNine : (QuadraticAlgebra.omega : QuadraticFieldTwentyNine) ^ 2 = 1 + 5 * QuadraticAlgebra.omega := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add, Algebra.smul_def, Algebra.smul_def]
  simp

def fundamentalUnitSqrtTwentyNine : 𝓞 QuadraticFieldTwentyNine := ⟨QuadraticAlgebra.omega, Polynomial.X ^ 2 - Polynomial.C 5 * Polynomial.X - 1,
  by monicity!, by simp [omega_sq_sqrtTwentyNine]⟩

theorem fundamentalUnit_sq : fundamentalUnitSqrtTwentyNine ^ 2 = 1 + 5 * fundamentalUnitSqrtTwentyNine := by
  refine RingOfIntegers.ext ?_
  simp only [map_pow, map_add, map_mul, map_one, map_ofNat]
  exact omega_sq_sqrtTwentyNine

def tateCurveSqrtTwentyNine : _root_.WeierstrassCurve (𝓞 QuadraticFieldTwentyNine) := ⟨1, 0, fundamentalUnitSqrtTwentyNine ^ 2, 0, 0⟩

theorem tateCurve_discriminant : tateCurveSqrtTwentyNine.Δ = -fundamentalUnitSqrtTwentyNine ^ 10 := by
  simp only [tateCurveSqrtTwentyNine, _root_.WeierstrassCurve.Δ, _root_.WeierstrassCurve.b₂,
    _root_.WeierstrassCurve.b₄, _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈]
  linear_combination (fundamentalUnitSqrtTwentyNine ^ 8 + 5 * fundamentalUnitSqrtTwentyNine ^ 7 - fundamentalUnitSqrtTwentyNine ^ 6) * fundamentalUnit_sq

instance : tateCurveSqrtTwentyNine.IsElliptic := ⟨tateCurve_discriminant ▸ ((IsUnit.of_mul_eq_one (fundamentalUnitSqrtTwentyNine - 5)
  (by linear_combination fundamentalUnit_sq)).pow 10).neg⟩

theorem Surf.exists_g_eq_one : ∃ s : Surf, s.A.g = 1 :=
  have ⟨s, _, _, h, _⟩ := Surf.exists_const QuadraticFieldTwentyNine tateCurveSqrtTwentyNine
  ⟨s, h⟩

instance : Nonempty Surf := Surf.exists_g_eq_one.nonempty

theorem SurfFp.exists_const (p : ℕ) [Fact p.Prime] (W : _root_.WeierstrassCurve (ZMod p))
    [W.IsElliptic] : ∃ (C : ProjCode (ZMod p)) (h : IsProjSurface (ZMod p) C.X) (A : PPCode C.X)
      (φ : A.P.A.left ⟶ (WeierstrassCurve.ellPolAV W).A.left),
        Nonempty (C.X ≅ PSpace (ZMod p) 2) ∧ (SurfFp.mk p C h A).A.g = 1 ∧
        A.P.IsPull (.ofPolAV (WeierstrassCurve.ellPolAV W)) C.str φ := by
  obtain ⟨C, e, -⟩ := ProjCode.exists_iso (ProjSpace.isProjOver_str (ZMod p) 2)
  obtain ⟨Q, φ, hg, H⟩ := PPCode.exists_const (WeierstrassCurve.ellPolAV W) le_rfl C.isProjOver
  have := ProjSpace.isIntegral_of_isDomain (ZMod p) 2
  exact ⟨C, ⟨.of_isIso e.inv, (IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso e).isHomeomorph).trans (ProjSpace.topologicalKrullDim_eq _ 2),
    C.strHom_eq ▸ C.isProjOver⟩, Q, φ, ⟨e⟩, hg, H⟩

theorem SurfFp.secondChernFinite_constantFamily (s : SurfFp) (P : PPAS (Sp (ZMod s.p))) (hg : P.g = 1) (hs : s.A.g = 1)
    {φ : s.A.P.A.left ⟶ P.A.left} (H : s.A.P.IsPull P s.C.str φ) : s.ch2Q = 0 := by
  obtain ⟨U, t, hU, ht⟩ := (hg ▸ P.isVB_omega : IsVB (omega P.A) 1) (IsLocalRing.closedPoint _)
  obtain rfl : U = ⊤ := top_le_iff.1 fun x _ => by
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint _)]
  have e : omega s.A.P.A ≅ structureModule s.C.X :=
    (omegaPullIso H).symm ≪≫ (ht.pullback s.C.str).iso (isFrame_one ⊤)
  have e' : dual (structureModule s.C.X) ≅ structureModule s.C.X :=
    (isFrame_one ⊤).dual.iso (isFrame_one ⊤)
  rw [ch2Q, IndefiniteRowSideFullHecke.ZeroSectionBase.degCh2_congr e, hs, degCh2, chi_congr _ e']
  simp [two_mul]

theorem SurfFp.exists_g_eq_one (p : ℕ) [Fact p.Prime] :
    ∃ s : SurfFp, s.p = p ∧ s.A.g = 1 ∧ s.ch2Q = 0 :=
  have ⟨C, h, A, _, _, hg, H⟩ := SurfFp.exists_const p (.ofJ 0)
  ⟨.mk p C h A, rfl, hg, SurfFp.secondChernFinite_constantFamily _ _ rfl hg H⟩

instance : Nonempty SurfFp := have ⟨s, _⟩ := SurfFp.exists_g_eq_one 2; ⟨s⟩

end GlobalTheory.ShFam.Pad
