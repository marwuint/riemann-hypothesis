import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F]

abbrev Pts (Y : Var F) (σ : F →+* ℂ) : Type := CxPts Y.str σ

structure CxSt (F : Type) [Field F] [NumberField F] : Type 1 where

  [ptsMeas : ∀ (Y : Var F) σ, MeasurableSpace (Pts Y σ)]

  borel : ∀ (Y : Var F) σ, BorelSpace (Pts Y σ)

  vol : ∀ (Y : Var F) σ, Measure (Pts Y σ)

  FnC : Var F → (F →+* ℂ) → Type

  [fnCRing : ∀ Y σ, CommRing (FnC Y σ)]

  [fnCAlg : ∀ Y σ, Algebra ℂ (FnC Y σ)]

  cx : ∀ Y σ, Y.Fn →+* FnC Y σ

  cx_smul : ∀ Y σ (a : F) (f : Y.Fn), cx Y σ (a • f) = σ a • cx Y σ f

  Met : ∀ Y : Var F, (F →+* ℂ) → Y.Dv → Type

  mAdd : ∀ Y σ Δ Δ', Met Y σ Δ → Met Y σ Δ' → Met Y σ (Δ + Δ')

  mPow : ∀ Y σ Δ (k : ℕ), Met Y σ Δ → Met Y σ (k • Δ)

  fsMet : ∀ Y σ Δ {k : Type} [Fintype k], (k → FnC Y σ) → Met Y σ Δ

  pn : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → Pts Y σ → ℝ

  pnK : ∀ Y σ Δ, Met Y σ Δ → FnC Y σ → Pts Y σ → ℝ

  mSmooth : ∀ Y σ Δ, Met Y σ Δ → Prop

  mPsh : ∀ Y σ Δ, Met Y σ Δ → (Pts Y σ → ℝ) → Prop

  redZero : ∀ (Y : Var F) σ, Y.Dv → (Fin Y.dim → FnC Y σ) → Set (Pts Y σ) → Prop

  agreeOn : ∀ (Y : Var F) σ, Y.Dv → FnC Y σ → FnC Y σ → Set (Pts Y σ) → Prop

  resNorm : ∀ Y σ Δ, Met Y σ Δ → ∀ Δs, Met Y σ Δs → (Fin Y.dim → FnC Y σ) → FnC Y σ → Pts Y σ → ℝ

  regOn : ∀ (Y : Var F) σ, Y.Dv → FnC Y σ → Set (Pts Y σ) → Prop

  ofWeight : ∀ (Y : Var F) σ (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), Presents Δ L r → Weight Y.str σ L → Met Y σ Δ

  pn_ofWeight : ∀ (Y : Var F) σ (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (h : Presents Δ L r) (φ : Weight Y.str σ L)
    (f : Y.Fn) (y : Pts Y σ) (i : L.ι), under y ∈ L.U i → Δ.RegularAt (under y) f →
      pn Y σ Δ (ofWeight Y σ Δ L r h φ) (cx Y σ f) y = ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-φ.φ i y)

  pn_mAdd : ∀ (Y : Var F) σ (Δ Δ' : Y.Dv) (m : Met Y σ Δ) (m' : Met Y σ Δ') (f f' : Y.Fn) (y : Pts Y σ),
    Δ.RegularAt (under y) f → Δ'.RegularAt (under y) f' →
      pn Y σ _ (mAdd Y σ Δ Δ' m m') (cx Y σ (f * f')) y = pn Y σ Δ m (cx Y σ f) y * pn Y σ Δ' m' (cx Y σ f') y

  pn_mPow : ∀ (Y : Var F) σ (Δ : Y.Dv) (k : ℕ) (m : Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ), Δ.GeneratesAt (under y) f →
      pn Y σ _ (mPow Y σ Δ k m) (cx Y σ (f ^ k)) y = pn Y σ Δ m (cx Y σ f) y ^ k

  pn_mul : ∀ (Y : Var F) σ (Δ : Y.Dv) (m : Met Y σ Δ) (a f : Y.Fn) (y : Pts Y σ), RegAt (under y) a →
    Δ.RegularAt (under y) f → pn Y σ Δ m (cx Y σ (a * f)) y = ‖ratVal a y‖ ^ 2 * pn Y σ Δ m (cx Y σ f) y

  pn_fs : ∀ (Y : Var F) σ (Δ : Y.Dv) {ι κ : Type} [Fintype ι] [Fintype κ] (b : ι → Y.Fn) (X : ι → κ → ℂ) (f : Y.Fn)
    (y : Pts Y σ) (g : Y.Fnˣ), Δ.IsEqn (under y) g → (∀ i, b i ∈ Y.H0 Δ) → Δ.RegularAt (under y) f →
    (∑ k, ‖∑ i, X i k * ratVal (b i * (g : Y.Fn)) y‖ ^ 2) ≠ 0 →
      pn Y σ Δ (fsMet Y σ Δ fun k => ∑ i, X i k • cx Y σ (b i)) (cx Y σ f) y =
        ‖ratVal (f * (g : Y.Fn)) y‖ ^ 2 / ∑ k, ‖∑ i, X i k * ratVal (b i * (g : Y.Fn)) y‖ ^ 2

  vol_eq : HEq vol fun (Y : Var F) σ => Var.vol Y σ := by rfl

  fnC_eq : FnC = fun (Y : Var F) σ => Var.FnC Y σ := by rfl

  fnCRing_eq : HEq fnCRing fun (Y : Var F) σ => (inferInstance : CommRing (Var.FnC Y σ)) := by rfl

  fnCAlg_eq : HEq fnCAlg fun (Y : Var F) σ => (inferInstance : Algebra ℂ (Var.FnC Y σ)) := by rfl

  cx_eq : HEq cx fun (Y : Var F) σ => Var.cx Y σ := by rfl

  met_eq : Met = fun (Y : Var F) σ Δ => Var.Met Y σ Δ := by rfl

  mAdd_eq : HEq mAdd fun (Y : Var F) σ Δ Δ' => Var.mAdd Y σ Δ Δ' := by rfl

  mPow_eq : HEq mPow fun (Y : Var F) σ Δ => Var.mPow Y σ Δ := by rfl

  fsMet_eq : HEq @fsMet fun (Y : Var F) σ Δ => @Var.fsMet F _ Y σ Δ := by rfl

  pn_eq : HEq pn fun (Y : Var F) σ Δ => Var.pn Y σ Δ := by rfl

  pnK_eq : HEq pnK fun (Y : Var F) σ Δ => Var.pnK Y σ Δ := by rfl

  mSmooth_eq : HEq mSmooth fun (Y : Var F) σ Δ => Var.mSmooth Y σ Δ := by rfl

  mPsh_eq : HEq mPsh fun (Y : Var F) σ Δ => Var.mPsh Y σ Δ := by rfl

  redZero_eq : HEq redZero fun (Y : Var F) σ Δ => Var.redZero Y σ Δ := by rfl

  agreeOn_eq : HEq agreeOn fun (Y : Var F) σ Δ => Var.agreeOn Y σ Δ := by rfl

  resNorm_eq : HEq resNorm fun (Y : Var F) σ Δ => Var.resNorm Y σ Δ := by rfl

  regOn_eq : HEq regOn fun (Y : Var F) σ Δ => Var.regOn Y σ Δ := by rfl

  ofWeight_eq : HEq ofWeight fun (Y : Var F) σ Δ L r => Var.ofWeight Y σ Δ L r := by rfl

attribute [instance] CxSt.fnCRing CxSt.fnCAlg

namespace CxSt

variable (F) in
open Var in

@[reducible] def std : CxSt F where
  borel _ _ := inferInstance
  vol := Var.vol
  FnC := Var.FnC
  cx := Var.cx
  cx_smul := Var.cx_smul
  Met := Var.Met
  mAdd Y σ Δ Δ' := Var.mAdd Y σ Δ Δ'
  mPow Y σ Δ := Var.mPow Y σ Δ
  fsMet Y σ Δ := Var.fsMet Y σ Δ
  pn Y σ Δ := Var.pn Y σ Δ
  pnK Y σ Δ := Var.pnK Y σ Δ
  mSmooth Y σ Δ := Var.mSmooth Y σ Δ
  mPsh Y σ Δ := Var.mPsh Y σ Δ
  redZero Y σ Δ := Var.redZero Y σ Δ
  agreeOn Y σ Δ := Var.agreeOn Y σ Δ
  resNorm Y σ Δ := Var.resNorm Y σ Δ
  regOn Y σ Δ := Var.regOn Y σ Δ
  ofWeight Y σ Δ L r := Var.ofWeight Y σ Δ L r
  pn_ofWeight Y σ Δ L r h φ f y i hi _ := by rw [Var.pn_ofWeight h φ (CxPts.mem_ptsIn.2 hi), fval_cx]
  pn_mAdd Y σ Δ Δ' m m' f f' y h h' := by
    rw [map_mul, Var.pn_mAdd (secReg_cx_iff.2 h) (secReg_cx_iff.2 h')]
  pn_mPow Y σ Δ k m f y h := by rw [map_pow, Var.pn_mPow (secReg_cx_iff.2 h.regularAt)]
  pn_mul Y σ Δ m a f y ha h := by
    rw [map_mul, Var.pn_mul (regC_cx_iff.2 ha) (secReg_cx_iff.2 h), val_cx]
  pn_fs Y σ Δ ι κ _ _ b X f y g hg hb _ _ := by
    have e (k) := hasVal_sum_smul (y := y) hg (fun i => secReg_cx_of_mem (hb i) y) fun i => X i k
    rw [pn_fsMet (fun k => (secReg_iff hg).2 (e k).regC) hg, fval_cx]
    simp only [fval, fun k => (e k).val_eq, ← map_mul, val_cx]

theorem eq_std (C : CxSt F) : C = std F := by
  obtain @⟨μ, hμ, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    h₁, rfl, h₃, h₄, h₅, rfl, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈⟩ := C
  obtain rfl : μ = (std F).ptsMeas :=
    funext fun Y => funext fun σ => (hμ Y σ).measurable_eq.trans ((std F).borel Y σ).measurable_eq.symm
  cases h₁; cases h₃; cases h₄; cases h₅; cases h₇; cases h₈; cases h₉; cases h₁₀; cases h₁₁; cases h₁₂; cases h₁₃
  cases h₁₄; cases h₁₅; cases h₁₆; cases h₁₇; cases h₁₈
  rfl

instance : Unique (CxSt F) := ⟨⟨std F⟩, eq_std⟩

variable (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (Δ : Y.Dv) (m : C.Met Y σ Δ)

end CxSt

abbrev below {K : Type} [Field K] {Z : Scheme.{0}} (y : Sp K ⟶ Z) : Z := y (IsLocalRing.closedPoint K)

open Classical in

def valAt {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (f : Z.functionField) : K :=
  if h : RegAt (below y) f then (Scheme.stalkClosedPointTo y).hom h.choose else 0

def eqn {Z : Scheme.{0}} [IsIntegral Z] (Δ : CartierDiv Z) (x : Z) : Z.functionFieldˣ := (Δ.exists_isEqn x).choose

structure Ext (v : HeightOneSpectrum (𝓞 F)) : Type where

  w : AbsoluteValue (AlgebraicClosure F) ℝ

  w_alg : ∀ a : F, w (algebraMap F _ a) = NumberField.HeightOneSpectrum.adicAbv F v a

  O : ValuationSubring (AlgebraicClosure F)

  mem_O : ∀ x, x ∈ O ↔ w x ≤ 1

instance Ext.instNonempty (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := IsAlgClosed.lift
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

def AlgPt (Y : Var F) : Type :=
  {y : Sp (AlgebraicClosure F) ⟶ Y.X // y ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))}

structure Adl (C : CxSt F) (Y : Var F) : Type where

  D : Y.Dv

  n : ℕ+

  m : ∀ σ, C.Met Y σ D

  ci : InfinitePlace F → ℝ

  lg : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

structure Model (Y : Var F) : Type 1 where

  X : Scheme.{0}

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  j : Y.X ⟶ X

  pb : IsPullback j Y.str p (spMap (algebraMap (𝓞 F) F))

namespace Adl

variable {C : CxSt F} {Y : Var F} (A : Adl C Y)

def twist (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ) : Adl C Y :=
  { A with ci := A.ci + ci, lg := fun v e y => A.lg v e y - (A.n : ℕ) * cf v }

def deg : ℝ := (Y.inter (fun _ => A.D) : ℝ) / ((A.n : ℕ) : ℝ) ^ Y.dim

def secs (τ : ℕ) : Set Y.Fn := {f | f ^ (A.n : ℕ) ∈ Y.H0 (τ • A.D)}

def nrmInf (σ : F →+* ℂ) (τ : ℕ) (f : Y.Fn) (y : Pts Y σ) : ℝ :=
  Real.exp (-((τ : ℝ) * A.ci (InfinitePlace.mk σ))) *
    C.pn Y σ (τ • A.D) (C.mPow Y σ A.D τ (A.m σ)) (C.cx Y σ (f ^ (A.n : ℕ))) y ^ (1 / (2 * ((A.n : ℕ) : ℝ)))

def nrmFin (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) (e : Ext v) (y : AlgPt Y) : ℝ :=
  e.w (valAt y.1 (f ^ (A.n : ℕ) * (eqn A.D (below y.1) : Y.Fn) ^ τ)) ^ (1 / ((A.n : ℕ) : ℝ)) *
    Real.exp ((τ : ℝ) * A.lg v e y / ((A.n : ℕ) : ℝ))

def supInf (v : InfinitePlace F) (τ : ℕ) (f : Y.Fn) : ℝ := ⨆ y, A.nrmInf v.embedding τ f y

def supFin (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) : ℝ :=
  ⨆ q : Ext v × AlgPt Y, A.nrmFin v τ f q.1 q.2

def small (τ : ℕ) : Set Y.Fn :=
  {f | f ∈ A.secs τ ∧ (∀ σ y, A.nrmInf σ τ f y ≤ 1) ∧ ∀ v e y, A.nrmFin v τ f e y ≤ 1}

def arVol : ℝ :=
  (limsup (fun τ : ℕ => ENNReal.log ((A.small τ).encard : ENNReal) *
    ((((Y.dim + 1).factorial : ℝ) / (τ : ℝ) ^ (Y.dim + 1) : ℝ) : EReal)) atTop).toReal / (Module.finrank ℚ F : ℝ)

open Classical in

def ht (x : Y.X) : ℝ :=
  -((∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
        (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) +
    ∑ᶠ v : HeightOneSpectrum (𝓞 F), if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0) /
  (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ))

def Induced (M : Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) : Prop :=
  (Function.support cf).Finite ∧
  ∃ r : (L.B.pull M.j).ι → Y.Fnˣ, Presents ((k : ℕ) • A.D) (L.B.pull M.j) r ∧
    (∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))) (i : (L.B.pull M.j).ι) (f : Y.Fn),
      y'.1 = y.1 ≫ M.j → under y ∈ (L.B.pull M.j).U i → ((k : ℕ) • A.D).RegularAt (under y) f →
      Real.exp (-(2 * (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
        ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.B.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      (k : ℕ) * A.lg v e y =
        Real.log (e.w (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn))) - (k : ℕ) * (A.n : ℕ) * cf v

def IsArTop (t : ℝ) : Prop :=
  ∃ (M : Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (a : ℝ), A.Induced M L k cf ∧
    (haveI := M.ar.isIntegral; L.IsSelfInter a) ∧
    t = (a / (((k : ℕ) : ℝ) * (A.n : ℕ)) ^ (Y.dim + 1) + ((Y.dim : ℝ) + 1) * A.deg * ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ)

open Classical in

def arTop : ℝ := if h : ∃ t, A.IsArTop t then h.choose else 0

def SemiPos : Prop := ∀ σ, C.mSmooth Y σ A.D (A.m σ) ∧ C.mPsh Y σ A.D (A.m σ) 0

def NefFib : Prop := ∃ (M : Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
  A.Induced M L k cf ∧ ArInt.NefFib L

def Nef : Prop := A.SemiPos ∧ A.NefFib ∧ ∀ x : Y.X, IsClosed ({x} : Set Y.X) → 0 ≤ A.ht x

variable {A}

end Adl

namespace Base

theorem valAt_stalk {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem isEqn_eqn {Z : Scheme.{0}} [IsIntegral Z] (Δ : CartierDiv Z) (x : Z) : Δ.IsEqn x (eqn Δ x) :=
  (Δ.exists_isEqn x).choose_spec

theorem valAt_zpow {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f : Z.functionField}
    (hf : UnitAt (below y) f) : valAt y f ≠ 0 ∧ ∀ m : ℤ, valAt y (f ^ m) = valAt y f ^ m := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hf
  refine ⟨by rw [valAt_stalk]; exact (a.isUnit.map _).ne_zero, fun m => ?_⟩
  have e {S : Type} [Field S] (ψ : Z.presheaf.stalk (below y) →+* S) : ψ (a ^ m : _ˣ) = ψ a ^ m := by
    exact (congrArg Units.val (map_zpow (Units.map ψ.toMonoidHom) a m)).trans (Units.val_zpow_eq_zpow_val _ _)
  rw [← e, valAt_stalk, valAt_stalk, e]

omit [NumberField F] in

theorem ratVal_one {Y : Var F} {σ : F →+* ℂ} (y : Pts Y σ) : ratVal (1 : Y.Fn) y = 1 := by
  have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
  rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e

end Base

open Base

namespace Adl

variable {C : CxSt F} {Y : Var F} {A : Adl C Y} {M : Model Y} {L : HermLB M.p} {k : ℕ+}
  {cf : HeightOneSpectrum (𝓞 F) → ℝ}

variable (C Y) in

def triv : Adl C Y where
  D := 0
  n := 1
  m σ := C.ofWeight Y σ 0 (LB.triv Y.X) (fun _ => 1) presents_zero (Weight.ofFun fun _ => 0)
  ci := 0
  lg _ e y := -Real.log (e.w (valAt y.1 (eqn (0 : Y.Dv) (below y.1) : Y.Fn)))

end Adl

variable [StarRing F]

open Classical in

def frameAt (W : HLat F) (σ : F →+* ℂ) : Matrix W.ι W.ι ℂ :=
  if (InfinitePlace.mk σ).embedding = σ then W.X (InfinitePlace.mk σ) else (W.X (InfinitePlace.mk σ)).map (starRingEnd ℂ)

def ofW (C : CxSt F) (Y : Var F) (L : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn) : Adl C Y where
  D := L
  n := 1
  m σ := C.fsMet Y σ L fun k : W.ι => ∑ i, frameAt W σ i k • C.cx Y σ (ι (W.b i))
  ci := 0
  lg _ e y := -Real.log (⨆ x : W.L, e.w (valAt y.1 (ι x * (eqn L (below y.1) : Y.Fn))))

structure CutSt (C : CxSt F) : Type 1 where

  cutGood : ∀ Y : Var F, Y.Cl → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → Prop

  cutHt : ∀ Y : Var F, Adl C Y → ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → ℝ

  cutOrd : ∀ (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → Y.Dv → Y.Fn → ℕ

structure ResSt (C : CxSt F) : Type 1 where

  resFull : ∀ (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Y.Fn) → Adl C Y → Prop

  resDeg : ∀ (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    (Fin n → Y.Fn) → (Fin Y.dim → Fin n → 𝓞 E) → ∀ (M0 : HLat F), (M0.V →ₗ[F] Y.Fn) → Adl C Y → ℝ

omit [StarRing F] in

theorem supInf_twist {C : CxSt F} {Y : Var F} (A : Adl C Y) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) (v : InfinitePlace F) (τ : ℕ) (f : Y.Fn) :
    (A.twist ci cf).supInf v τ f = Real.exp (-((τ : ℝ) * ci v)) * A.supInf v τ f := by
  unfold Adl.supInf
  rw [Real.mul_iSup_of_nonneg (Real.exp_pos _).le]
  refine congrArg _ (funext fun y => ?_)
  simp only [Adl.nrmInf, Adl.twist, InfinitePlace.mk_embedding, Pi.add_apply]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

omit [StarRing F] in

theorem supFin_twist {C : CxSt F} {Y : Var F} (A : Adl C Y) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) :
    (A.twist ci cf).supFin v τ f = Real.exp (-((τ : ℝ) * cf v)) * A.supFin v τ f := by
  unfold Adl.supFin
  rw [Real.mul_iSup_of_nonneg (Real.exp_pos _).le]
  refine congrArg _ (funext fun q => ?_)
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  simp only [Adl.nrmFin, Adl.twist]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem supInf_ofW (C : CxSt F) (Y : Var F) (L : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn) (v : InfinitePlace F) (τ : ℕ)
    (f : Y.Fn) : (ofW C Y L W ι).supInf v τ f =
      ⨆ y, Real.sqrt (C.pn Y v.embedding (τ • L) (C.mPow Y v.embedding L τ
        (C.fsMet Y v.embedding L (fun k : W.ι => ∑ i, (W.X v) i k • C.cx Y v.embedding (ι (W.b i)))))
        (C.cx Y v.embedding f) y) := by
  unfold Adl.supInf
  refine congrArg _ (funext fun y => ?_)
  have e : frameAt W v.embedding = W.X v := by simp [frameAt]
  simp [Adl.nrmInf, ofW, e, Real.sqrt_eq_rpow]

def geoOf (C : CxSt F) (K : CutSt C) (R : ResSt C) : DV.Geo F where
  Var := Var F
  dim := Var.dim
  Fn := Var.Fn
  Dv := Var.Dv
  Eff := Var.Eff
  eff_zero := Var.eff_zero
  eff_add := Var.eff_add
  H0 := Var.H0
  degreeZeroCohomology_finiteDimensional := riemannRoch_finite F
  mul_mem_riemannRochSpace_add := Var.mul_mem_riemannRochSpace_add
  riemannRoch_mono := Var.riemannRoch_mono
  KY := Var.KY
  Cl := Var.Cl
  properCl := Var.properCl
  subCl := Var.subCl
  supp := Var.supp
  inter := Var.inter
  nef := Var.nef
  big := Var.big
  bpf := Var.bpf
  phiBir := Var.phiBir
  phiNoContr := Var.phiNoContr
  vanishOn := Var.vanishOn
  hdim := Var.hdim
  pts := Pts
  ptsMeas := C.ptsMeas
  vol := C.vol
  FnC := C.FnC
  cx := C.cx
  cx_smul := C.cx_smul
  Met := C.Met
  mAdd := C.mAdd
  mPow := C.mPow
  fsMet := C.fsMet
  pn := C.pn
  pnK := C.pnK
  mSmooth := C.mSmooth
  mPsh := C.mPsh
  redZero := C.redZero
  agreeOn := C.agreeOn
  resNorm := C.resNorm
  Adl := Adl C
  ofW := ofW C
  twist := fun _ => Adl.twist
  arTop := fun _ => Adl.arTop
  arVol := fun _ => Adl.arVol
  nefA := fun _ => Adl.Nef
  supInf := fun _ => Adl.supInf
  supFin := fun _ => Adl.supFin
  cutGood := K.cutGood
  cutHt := K.cutHt
  cutOrd := K.cutOrd
  resFull := R.resFull
  resDeg := R.resDeg
  supInf_ofW := supInf_ofW C
  supInf_twist := fun _ A ci cf _ => supInf_twist A ci cf
  supFin_twist := fun _ A ci cf _ => supFin_twist A ci cf
  regOn := C.regOn

theorem deg_ofW (C : CxSt F) (Y : Var F) (L : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn) :
    (ofW C Y L W ι).deg = (Y.inter (fun _ => L) : ℝ) := by simp [Adl.deg, ofW]

omit [StarRing F] in

theorem deg_twist {C : CxSt F} {Y : Var F} (A : Adl C Y) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : (A.twist ci cf).deg = A.deg := rfl

end GlobalTheory.TrueGeo
