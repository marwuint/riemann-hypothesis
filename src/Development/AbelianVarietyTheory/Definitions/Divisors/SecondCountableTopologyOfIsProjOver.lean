import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff TensorProduct
open MeasureTheory ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

namespace GlobalTheory

variable {k : Type} [CommRing k] {Y : Scheme.{0}}

open CxPts

structure AnRead (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) where

  ι : Type

  chart : ι → AlgChart p σ D

  cover : ∀ y, ∃ i, y ∈ (chart i).e.source

namespace AnRead

variable {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

variable (p σ D) in

def all [SmoothOfRelativeDimension D p] : AnRead p σ D := ⟨_, id, AlgChart.exists_mem_source⟩

instance nonempty [SmoothOfRelativeDimension D p] : Nonempty (AnRead p σ D) := ⟨all p σ D⟩

variable (R R' : AnRead p σ D) {S T : Set (CxPts p σ)}

theorem exists_finite [CompactSpace (CxPts p σ)] :
    ∃ s : Finset R.ι, ∀ y, ∃ i ∈ s, y ∈ (R.chart i).e.source := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ (fun i => (R.chart i).e.open_source)
    fun y _ => mem_iUnion.2 (R.cover y)
  exact ⟨s, fun y => by simpa using hs (mem_univ y)⟩

def HoloOn (S : Set (CxPts p σ)) (f : CxPts p σ → ℂ) : Prop :=
  ∀ i, DifferentiableOn ℂ (f ∘ (R.chart i).e.symm)
    ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S)

def SmoothOn (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (f ∘ (R.chart i).e.symm) ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S)

theorem holoOn_ev (W : Y.Opens) (f : Γ(Y, W)) : R.HoloOn (ptsIn p σ W) (ev p σ W f) :=
  fun i => (R.chart i).holo W f

variable {R}

theorem exists_eventuallyEq (c : AlgChart p σ D) {v : V D} (hv : v ∈ c.e.target) {E : Type*}
    (f : CxPts p σ → E) : ∃ i, c.e.symm v ∈ (R.chart i).e.source ∧
      f ∘ c.e.symm =ᶠ[𝓝 v] (f ∘ (R.chart i).e.symm) ∘ (R.chart i).e ∘ c.e.symm := by
  obtain ⟨i, hi⟩ := R.cover (c.e.symm v)
  exact ⟨i, hi, eventually_of_mem ((isOpen_over c.e (R.chart i).e.open_source).mem_nhds ⟨hv, hi⟩)
    fun w hw => (congrArg f ((R.chart i).e.left_inv hw.2)).symm⟩

theorem HoloOn.chart {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (hS : IsOpen S) (c : AlgChart p σ D) :
    DifferentiableOn ℂ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) := fun v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq (R := R) c hv.1 f
  exact ((((h i).differentiableAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    ((c.holo_trans _).differentiableAt ((isOpen_over _ (R.chart i).e.open_source).mem_nhds
      ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).differentiableWithinAt

theorem SmoothOn.chart {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    (c : AlgChart p σ D) : ContDiffOn ℝ ∞ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S) :=
  fun v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq (R := R) c hv.1 f
  have ho := isOpen_over c.e (R.chart i).e.open_source
  have ht : ContDiffOn ℝ ∞ ((R.chart i).e ∘ c.e.symm) _ := (contDiffOn_piLp 2).2 fun a =>
    contDiffOn_real ho (differentiableOn_euclidean.1 (c.holo_trans _) a)
  exact ((((h i).contDiffAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (ht.contDiffAt (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).contDiffWithinAt

theorem holoOn_iff (R R' : AnRead p σ D) (hS : IsOpen S) {f : CxPts p σ → ℂ} :
    R.HoloOn S f ↔ R'.HoloOn S f := ⟨fun h _ => h.chart hS _, fun h _ => h.chart hS _⟩

theorem smoothOn_iff (R R' : AnRead p σ D) (hS : IsOpen S) {f : CxPts p σ → ℝ} :
    R.SmoothOn S f ↔ R'.SmoothOn S f := ⟨fun h _ => h.chart hS _, fun h _ => h.chart hS _⟩

theorem HoloOn.mono {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (e : T ⊆ S) : R.HoloOn T f :=
  fun i => (h i).mono fun _ hv => ⟨hv.1, e hv.2⟩

theorem SmoothOn.mono {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (e : T ⊆ S) : R.SmoothOn T f :=
  fun i => (h i).mono fun _ hv => ⟨hv.1, e hv.2⟩

theorem HoloOn.congr {f g : CxPts p σ → ℂ} (h : R.HoloOn S f) (e : ∀ y ∈ S, g y = f y) :
    R.HoloOn S g := fun i => (h i).congr fun _ hv => e _ hv.2

theorem SmoothOn.congr {f g : CxPts p σ → ℝ} (h : R.SmoothOn S f) (e : ∀ y ∈ S, g y = f y) :
    R.SmoothOn S g := fun i => (h i).congr fun _ hv => e _ hv.2

theorem continuousOn_of_charts {E : Type*} [TopologicalSpace E] {f : CxPts p σ → E} (hS : IsOpen S)
    (h : ∀ i, ContinuousOn (f ∘ (R.chart i).e.symm)
      ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S)) : ContinuousOn f S := fun y hy => by
  obtain ⟨i, hi⟩ := R.cover y
  refine ((((h i).continuousAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hy))).comp
    ((R.chart i).e.continuousAt hi)).congr ?_).continuousWithinAt
  exact eventually_of_mem ((R.chart i).e.open_source.mem_nhds hi) fun z hz =>
    congrArg f ((R.chart i).e.left_inv hz)

theorem HoloOn.continuousOn {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (hS : IsOpen S) :
    ContinuousOn f S := continuousOn_of_charts hS fun i => (h i).continuousOn

theorem SmoothOn.continuousOn {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S) :
    ContinuousOn f S := continuousOn_of_charts hS fun i => (h i).continuousOn

theorem HoloOn.smoothOn_log {f : CxPts p σ → ℂ} (h : R.HoloOn S f) (hS : IsOpen S)
    (h0 : ∀ y ∈ S, f y ≠ 0) : R.SmoothOn S fun y => Real.log (‖f y‖ ^ 2) :=
  fun i => contDiffOn_log_normSq (isOpen_over _ hS) (h i) fun _ hv => h0 _ hv.2

end AnRead

variable {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AnRead

variable {R : AnRead p σ D} {A B : LB Y} {S : Set (CxPts p σ)}

theorem holoOn_of_chart (c : AlgChart p σ D) {f : CxPts p σ → ℂ}
    (h : DifferentiableOn ℂ (f ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) :
    R.HoloOn (c.e.source ∩ S) f := fun i =>
  (h.comp (((R.chart i).holo_trans c).mono fun _ hv => ⟨hv.1, hv.2.1⟩)
    fun _ hv => mem_over _ hv.2.1 hv.2.2).congr fun _ hv => congrArg f (c.e.left_inv hv.2.1).symm

theorem holoOn_of_cover {ι : Type*} {T : ι → Set (CxPts p σ)} (hT : ∀ j, IsOpen (T j))
    (hc : ∀ y ∈ S, ∃ j, y ∈ T j) {f : CxPts p σ → ℂ} (h : ∀ j, R.HoloOn (S ∩ T j) f) :
    R.HoloOn S f := fun i => differentiableOn_of_locally_differentiableOn fun _ hv => by
  obtain ⟨j, hj⟩ := hc _ hv.2
  exact ⟨_, isOpen_over (R.chart i).e (hT j), ⟨hv.1, hj⟩,
    (h j i).mono fun _ hw => ⟨hw.1.1, hw.1.2, hw.2.2⟩⟩

theorem smoothOn_of_cover {ι : Type*} {T : ι → Set (CxPts p σ)} (hT : ∀ j, IsOpen (T j))
    (hc : ∀ y ∈ S, ∃ j, y ∈ T j) {f : CxPts p σ → ℝ} (h : ∀ j, R.SmoothOn (S ∩ T j) f) :
    R.SmoothOn S f := fun i => contDiffOn_of_locally_contDiffOn fun _ hv => by
  obtain ⟨j, hj⟩ := hc _ hv.2
  exact ⟨_, isOpen_over (R.chart i).e (hT j), ⟨hv.1, hj⟩,
    (h j i).mono fun _ hw => ⟨hw.1.1, hw.1.2, hw.2.2⟩⟩

theorem holoOn_ev_of_subset {W : Y.Opens} (f : Γ(Y, W)) (h : S ⊆ ptsIn p σ W) :
    R.HoloOn S (ev p σ W f) := (R.holoOn_ev W f).mono h

theorem HoloOn.mul {f g : CxPts p σ → ℂ} (hf : R.HoloOn S f) (hg : R.HoloOn S g) :
    R.HoloOn S fun y => f y * g y := fun i => (hf i).mul (hg i)

theorem HoloOn.zpow {f : CxPts p σ → ℂ} (hf : R.HoloOn S f) (h0 : ∀ y ∈ S, f y ≠ 0) (n : ℤ) :
    R.HoloOn S fun y => f y ^ n := fun i => (hf i).zpow (Or.inl fun _ hv => h0 _ hv.2)

theorem HoloOn.inv {f : CxPts p σ → ℂ} (hf : R.HoloOn S f) (h0 : ∀ y ∈ S, f y ≠ 0) :
    R.HoloOn S fun y => (f y)⁻¹ := fun i => (hf i).inv fun _ hv => h0 _ hv.2

variable (R B) in

def holSec : Submodule ℂ (B.ι → CxPts p σ → ℂ) where
  carrier := {s | s ∈ fibSec p σ B ∧ ∀ i, R.HoloOn (ptsIn p σ (B.U i)) (s i)}
  zero_mem' := ⟨zero_mem _, fun _ _ => differentiableOn_const (0 : ℂ)⟩
  add_mem' hs ht := ⟨add_mem hs.1 ht.1, fun i j => (hs.2 i j).add (ht.2 i j)⟩
  smul_mem' c _ hs := ⟨Submodule.smul_mem _ c hs.1, fun i j => (hs.2 i j).const_smul c⟩

variable (R) in

theorem secVal_mem_holSec (s : B.Sec) : secVal p σ s ∈ R.holSec B :=
  ⟨secVal_mem s, fun _ => R.holoOn_ev _ _⟩

variable (R B) in

def valC : SecC p σ B →ₗ[ℂ] R.holSec B :=
  SecC.val.codRestrict _ (SecC.val_mem_of R.secVal_mem_holSec)

@[simp] theorem coe_valC (x : SecC p σ B) : (R.valC B x : B.ι → CxPts p σ → ℂ) = SecC.val x := rfl

end AnRead

namespace Weight

open AnRead

variable {R : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B}

def IsSmooth (φ : Weight p σ B) (R : AnRead p σ D) : Prop :=
  ∀ i, R.SmoothOn (ptsIn p σ (B.U i)) (φ.φ i)

def SemiPos (φ : Weight p σ B) (R : AnRead p σ D) : Prop :=
  ∀ (i : B.ι) (c : R.ι), ∀ y ∈ (R.chart c).e.source ∩ ptsIn p σ (B.U i), ∀ ξ : Fin D → ℂ,
    0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (φ.φ i ((R.chart c).e.symm v) : ℂ)) ((R.chart c).e y) ξ).re

def StrictPos (φ : Weight p σ B) (R : AnRead p σ D) : Prop :=
  ∀ (i : B.ι) (c : R.ι), ∀ y ∈ (R.chart c).e.source ∩ ptsIn p σ (B.U i), ∀ ξ : Fin D → ℂ, ξ ≠ 0 →
    0 < (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (φ.φ i ((R.chart c).e.symm v) : ℂ)) ((R.chart c).e y) ξ).re

theorem IsSmooth.addFn (h : φ.IsSmooth R) {u : CxPts p σ → ℝ} (hu : R.SmoothOn univ u) :
    (φ.addFn u).IsSmooth R := fun i c => (h i c).add (hu.mono (subset_univ _) c)

theorem IsSmooth.dual (h : φ.IsSmooth R) : φ.dual.IsSmooth R := fun i c => (h i c).neg

theorem IsSmooth.zpow (h : φ.IsSmooth R) (n : ℤ) : (φ.zpow n).IsSmooth R := fun j =>
  SmoothOn.congr (f := fun y => n * φ.φ (j PUnit.unit) y)
    (fun c => contDiffOn_const.mul ((h _).mono (fun _ => mem_pow_iff.1) c))
    fun y _ => φ.zpow_φ n j y

theorem isSmooth_fs {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ} (hB : B.IsLB)
    (he : ∀ a, e a ∈ R.holSec B) (h : NoCommonZero e) :
    (fs hB e (fun a => (he a).1) h).IsSmooth R := fun i c =>
  (ContDiffOn.sum (f := fun a v => ‖e a i ((R.chart c).e.symm v)‖ ^ 2) fun a _ =>
    (contDiffOn_real (isOpen_over _ (isOpen_ptsIn _)) ((he a).2 i c)).norm_sq ℂ).log
    fun _ hv => (h.sum_pos hv.2).ne'

theorem isSmooth_fsBasis {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB) (b : α → B.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (M : Matrix α α ℂ) (hM : M.det ≠ 0) :
    (fsBasis p σ hB b hb M hM).IsSmooth R :=
  isSmooth_fs hB (fun a => combVal_eq (p := p) (σ := σ) b M a ▸ (R.valC B _).2) _

def ofFun (u : CxPts p σ → ℝ) : Weight p σ (LB.triv Y) where
  isLB := LB.isLB_triv Y
  φ _ := u
  trans _ _ _ hi _ := by
    rw [gv_self (LB.isLB_triv Y) hi, norm_one, one_pow, Real.log_one, sub_zero]

end Weight

section Integral

variable [SmoothOfRelativeDimension D p] {B : LB Y} (K : CanonLB p D) (φ : Weight p σ B)
  (f : (tens K.bundle B).ι → CxPts p σ → ℂ)

namespace AlgChart

variable (c c' : AlgChart p σ D) {y : CxPts p σ}

def topCoeff (a : K.bundle.ι) (b : B.ι) (y : CxPts p σ) : ℂ :=
  rv σ c.isFrame (K.isFrame a) y * f (a, b) y

def topDens (y : CxPts p σ) : ℝ :=
  2 ^ D * (‖c.topCoeff K f (pick K.isLB y) (pick φ.isLB y) y‖ ^ 2 *
    Real.exp (-φ.φ (pick φ.isLB y) y))

end AlgChart

namespace AnRead

variable (R : AnRead p σ D)

def topMeasure : Measure (CxPts p σ) :=
  glueMeas (fun i => (R.chart i).e) fun i y => ENNReal.ofReal ((R.chart i).topDens K φ f y)

def topInt : ℝ≥0∞ := R.topMeasure K φ f univ

variable [SecondCountableTopology (CxPts p σ)]

end AnRead

end Integral

structure WeightFamily [SmoothOfRelativeDimension D p] (R : AnRead p σ D) (κ : Type) where

  K : CanonLB p D

  φK : Weight p σ K.bundle

  smoothK : φK.IsSmooth R

  L : κ → LB Y

  φ : ∀ a, Weight p σ (L a)

  smooth : ∀ a, (φ a).IsSmooth R

namespace WeightFamily

open AnRead

variable [SmoothOfRelativeDimension D p] {R : AnRead p σ D} {κ : Type} (F : WeightFamily R κ)

abbrev Idx : Type := R.ι × F.K.bundle.ι × ∀ a, (F.L a).ι

def dom (c : F.Idx) : Set (CxPts p σ) :=
  ptsIn p σ (F.K.bundle.U c.2.1) ∩ ⋂ a, ptsIn p σ ((F.L a).U (c.2.2 a))

variable [Fintype κ]

def refine : AnRead p σ D where
  ι := F.Idx
  chart c := (R.chart c.1).restr (F.dom c)
    ((isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun _ => isOpen_ptsIn _))
  cover y := by
    obtain ⟨i, hi⟩ := R.cover y
    exact ⟨(i, pick F.K.isLB y, fun a => pick (F.φ a).isLB y), hi, mem_pick F.K.isLB y,
      mem_iInter.2 fun a => mem_pick (F.φ a).isLB y⟩

variable {F} {c c' : F.Idx} {y : CxPts p σ}

theorem mem_U (h : y ∈ (F.refine.chart c).e.source) : y ∈ ptsIn p σ (R.chart c.1).U :=
  (R.chart c.1).source_subset h.1

theorem mem_K (h : y ∈ (F.refine.chart c).e.source) : y ∈ ptsIn p σ (F.K.bundle.U c.2.1) := h.2.1

theorem mem_L (h : y ∈ (F.refine.chart c).e.source) (a : κ) :
    y ∈ ptsIn p σ ((F.L a).U (c.2.2 a)) := mem_iInter.1 h.2.2 a

variable (F)

def g₀ : Option κ → F.Idx → F.Idx → CxPts p σ → ℂ
  | none, c, c' => rv σ (R.chart c.1).isFrame (R.chart c'.1).isFrame
  | some a, c, c' => gv p σ (F.L a) (c.2.2 a) (c'.2.2 a)

def ph₀ : Option κ → F.Idx → CxPts p σ → ℝ
  | none, c => fun y =>
      F.φK.φ c.2.1 y + Real.log (‖rv σ (R.chart c.1).isFrame (F.K.isFrame c.2.1) y‖ ^ 2)
  | some a, c => (F.φ a).φ (c.2.2 a)

variable [DecidableEq κ] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]

def atlas : WeightedAtlas D (CxPts p σ) F.Idx (Option κ → ℤ) :=
  freeAtlas (fun c => (F.refine.chart c).e) F.refine.cover
    (fun c c' => (F.refine.chart c).holo_trans (F.refine.chart c')) F.g₀
    (by
      rintro (_ | a) c c'
      · exact ((F.refine.chart c).holo _ _).mono fun v hv =>
          mem_ptsIn_inf.2 ⟨mem_U ((F.refine.chart c).e.map_target hv.1), mem_U hv.2⟩ |> And.intro hv.1
      · exact ((F.refine.chart c).holo _ _).mono fun v hv => mem_ptsIn_inf.2
          ⟨mem_L ((F.refine.chart c).e.map_target hv.1) a, mem_L hv.2 a⟩ |> And.intro hv.1)
    (by
      rintro (_ | a) c c' y h h'
      · exact rv_ne_zero _ _ (mem_U h) (mem_U h')
      · exact gv_ne_zero (mem_L h a) (mem_L h' a))
    (by
      rintro (_ | a) c c' c'' y h h' h''
      · exact (rv_mul _ _ _ (mem_U h) (mem_U h') (mem_U h'')).symm
      · exact (gv_mul (F.φ a).isLB (mem_L h a) (mem_L h' a) (mem_L h'' a)).symm)
    F.ph₀
    (by
      rintro (_ | a) c
      · refine ContDiffOn.add (((F.smoothK c.2.1) c.1).mono fun v hv =>
          ⟨hv.1, mem_K ((F.refine.chart c).e.map_target hv)⟩) ?_
        have hm (v) (hv : v ∈ (F.refine.chart c).e.target) := (F.refine.chart c).e.map_target hv
        exact contDiffOn_log_normSq (F.refine.chart c).e.open_target
          (((F.refine.chart c).holo _ _).mono fun v hv =>
            ⟨hv, mem_ptsIn_inf.2 ⟨mem_U (hm v hv), mem_K (hm v hv)⟩⟩)
          fun v hv => rv_ne_zero _ _ (mem_U (hm v hv)) (mem_K (hm v hv))
      · exact ((F.smooth a _) c.1).mono fun v hv =>
          ⟨hv.1, mem_L ((F.refine.chart c).e.map_target hv) a⟩)
    (by
      rintro (_ | a) c c' y h h'
      · have e₁ := rv_mul (R.chart c.1).isFrame (R.chart c'.1).isFrame (F.K.isFrame c'.2.1)
          (mem_U h) (mem_U h') (mem_K h')
        have e₂ := rv_mul (R.chart c.1).isFrame (F.K.isFrame c.2.1) (F.K.isFrame c'.2.1)
          (mem_U h) (mem_K h) (mem_K h')
        have e := (log_normSq_mul (rv_ne_zero _ _ (mem_U h) (mem_U h'))
          (rv_ne_zero _ _ (mem_U h') (mem_K h'))).symm.trans
          ((congrArg (fun z => Real.log (‖z‖ ^ 2)) (e₁.trans e₂.symm)).trans (log_normSq_mul
            (rv_ne_zero _ _ (mem_U h) (mem_K h)) (rv_ne_zero _ _ (mem_K h) (mem_K h'))))
        simp only [ph₀, g₀]
        rw [F.φK.trans _ _ y (mem_K h) (mem_K h'), gv_canon]
        linarith
      · exact (F.φ a).trans _ _ y (mem_L h a) (mem_L h' a))
    none fun c c' y h h' => rv_chart (F.refine.chart c) (F.refine.chart c') h h'

theorem atlas_chart (c : F.Idx) : F.atlas.chart c = (F.refine.chart c).e := rfl

theorem atlas_kap : F.atlas.kap = Pi.single none 1 := rfl

theorem atlas_g (m : Option κ → ℤ) (c c' : F.Idx) (y : CxPts p σ) :
    F.atlas.g m c c' y = ∏ o, F.g₀ o c c' y ^ m o := rfl

theorem atlas_ph (m : Option κ → ℤ) (c : F.Idx) (y : CxPts p σ) :
    F.atlas.ph m c y = ∑ o, m o * F.ph₀ o c y := rfl

structure Reading (B : LB Y) (m : Option κ → ℤ) where

  isLB : B.IsLB

  u : F.Idx → B.ι → CxPts p σ → ℂ

  holo : ∀ c i, R.HoloOn ((F.atlas.chart c).source ∩ ptsIn p σ (B.U i)) (u c i)

  ne : ∀ c i y, y ∈ (F.atlas.chart c).source → y ∈ ptsIn p σ (B.U i) → u c i y ≠ 0

  compat : ∀ c c' i i' y, y ∈ (F.atlas.chart c).source → y ∈ (F.atlas.chart c').source →
    y ∈ ptsIn p σ (B.U i) → y ∈ ptsIn p σ (B.U i') →
    F.atlas.g m c c' y * u c' i' y = u c i y * gv p σ B i i' y

namespace Reading

variable {F} {A B : LB Y} {m m' : Option κ → ℤ} (r : F.Reading B m) {s t : B.ι → CxPts p σ → ℂ}

def read : (B.ι → CxPts p σ → ℂ) →ₗ[ℂ] (F.Idx → CxPts p σ → ℂ) where
  toFun s c y := r.u c (pick r.isLB y) y * s (pick r.isLB y) y
  map_add' _ _ := funext₂ fun _ _ => mul_add _ _ _
  map_smul' _ _ := funext₂ fun _ _ => mul_left_comm _ _ _

def Isometric (φ : Weight p σ B) : Prop :=
  ∀ c i y, y ∈ (F.atlas.chart c).source → y ∈ ptsIn p σ (B.U i) →
    F.atlas.ph m c y = φ.φ i y + Real.log (‖r.u c i y‖ ^ 2)

def cast (h : m = m') : F.Reading B m' :=
  ⟨r.isLB, r.u, r.holo, r.ne, h ▸ r.compat⟩

@[simp] theorem read_cast (h : m = m') : (r.cast h).read = r.read := rfl

def tens (r' : F.Reading A m') (r : F.Reading B m) : F.Reading (tens A B) (m' + m) where
  isLB := isLB_tens r'.isLB r.isLB
  u c i y := r'.u c i.1 y * r.u c i.2 y
  holo c i := ((r'.holo c i.1).mono (inter_subset_inter_right _ (ptsIn_mono inf_le_left))).mul
    ((r.holo c i.2).mono (inter_subset_inter_right _ (ptsIn_mono inf_le_right)))
  ne c i y h hi := mul_ne_zero (r'.ne c _ y h (mem_ptsIn_inf.1 hi).1) (r.ne c _ y h (mem_ptsIn_inf.1 hi).2)
  compat c c' i i' y h h' hi hi' := by
    rw [F.atlas.g_add _ _ _ _ _ h h', gv_tens hi hi', mul_mul_mul_comm,
      r'.compat c c' i.1 i'.1 y h h' (mem_ptsIn_inf.1 hi).1 (mem_ptsIn_inf.1 hi').1,
      r.compat c c' i.2 i'.2 y h h' (mem_ptsIn_inf.1 hi).2 (mem_ptsIn_inf.1 hi').2, mul_mul_mul_comm]

variable {r} in

theorem Isometric.tens {r' : F.Reading A m'} {ψ : Weight p σ A} {φ : Weight p σ B}
    (h' : r'.Isometric ψ) (h : r.Isometric φ) : (r'.tens r).Isometric (ψ.tens φ) :=
  fun c i y hc hi => by
  have e := mem_ptsIn_inf.1 hi
  rw [F.atlas.ph_add _ _ _ _ hc, h' c _ y hc e.1, h c _ y hc e.2]
  simp only [Reading.tens, Weight.tens, log_normSq_mul (r'.ne c _ y hc e.1) (r.ne c _ y hc e.2)]
  ring

def zpow (n : ℤ) : F.Reading (LB.LinComb B (K := PUnit) (fun _ => 𝟙 Y) fun _ => n) (n • m) where
  isLB := Semi.LB.isLB_linComb r.isLB _ _
  u c j y := r.u c (j PUnit.unit) y ^ n
  holo c j := ((r.holo c _).zpow (fun y hy => r.ne c _ y hy.1 hy.2) n).mono
    fun _ hy => ⟨hy.1, mem_pow_iff.1 hy.2⟩
  ne c j y h hj := zpow_ne_zero _ (r.ne c _ y h (mem_pow_iff.1 hj))
  compat c c' j j' y h h' hj hj' := by
    rw [gv_pow (mem_pow_iff.1 hj) (mem_pow_iff.1 hj'), ← mul_zpow,
      ← r.compat c c' _ _ y h h' (mem_pow_iff.1 hj) (mem_pow_iff.1 hj'), mul_zpow, atlas_g, atlas_g,
      ← Finset.prod_zpow]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm n, zpow_mul]

abbrev pow (n : ℕ) : F.Reading (lbPow B n) ((n : ℤ) • m) := r.zpow n

variable {r} in

theorem Isometric.zpow {φ : Weight p σ B} (h : r.Isometric φ) (n : ℤ) :
    (r.zpow n).Isometric (φ.zpow n) := fun c j y hc hj => by
  have e := h c _ y hc (mem_pow_iff.1 hj)
  rw [φ.zpow_φ n j y, show (r.zpow n).u c j y = r.u c (j PUnit.unit) y ^ n from rfl, log_normSq_zpow,
    ← mul_add, ← e, atlas_ph, atlas_ph, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_assoc]

end Reading

end WeightFamily

namespace CxPts

variable (σ)

theorem t2Space_cxPts_of_isProjOver (h : IsProjOver p) : T2Space (CxPts p σ) := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := isProper_str k N
  infer_instance

theorem secondCountableTopology_of_isProjOver (h : IsProjOver p) :
    SecondCountableTopology (CxPts p σ) := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := isProper_str k N
  infer_instance

end CxPts

namespace ProjAn

open ProjSpace

variable (k σ) (N : ℕ)

instance smooth : SmoothOfRelativeDimension N (PSpace.str k N) :=
  Adelic.smoothOfRelativeDimension_pspace k N

instance proper : IsProper (PSpace.str k N) := isProper_str k N

instance compact : CompactSpace (CxPts (PSpace.str k N) σ) := compactSpace_pSpace σ N

def fsO1 : Weight (PSpace.str k N) σ (O1 k N) :=
  Weight.fsBasis _ σ (O1_isLB k N) (coord k N) (iSup_nonzeroLocus_coord k N) 1 (by simp)

theorem fubiniStudyWeight_projPoint (v : Unimodular ℂ N) (i : Fin (N + 1)) (hi : v.1 i ≠ 0) :
    (fsO1 k σ N).φ i (projPt σ v) = Real.log (∑ a, ‖v.1 a / v.1 i‖ ^ 2) := by
  refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ (Finset.sum_congr rfl fun a _ => ?_))
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [div_eq_mul_inv, ← Ring.inverse_eq_inv, ← valR_pt_ratio σ v.1 v.2 hi.isUnit a]
  rfl

variable (K : CanonLB (PSpace.str k N) N)

end ProjAn

end GlobalTheory
