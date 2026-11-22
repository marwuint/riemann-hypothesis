import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory MeasureTheory
  NumberField TensorProduct GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

lemma point_self {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) :
    (self A N).point x = projPoint ρ x.1 :=
  (self A N).ι_point x

lemma rep_chartIndex_ne_zero (v : CP N) : v.rep (CP.chartIndex v) ≠ 0 := by
  have h := CP.mk_mem_chartDomain (CP.chartIndex v) v.rep v.rep_nonzero
  rw [Projectivization.mk_rep] at h
  exact h.mp (CP.mem_chartDomain_chartIndex v)

lemma point_mem_stdOpen {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) {j : Fin (N + 1)}
    (hj : x.1.rep j ≠ 0) : (self A N).point x ∈ ProjSpace.stdOpen A N j := by
  rw [point_self]
  change (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ∉ (projPoint ρ x.1).asHomogeneousIdeal
  intro h
  have := (isOver_projPoint ρ x.1 1 (MvPolynomial.X j) (ProjSpace.X_mem j)).1 h
  simp [evalAt] at this
  exact hj this

variable (A N) in

def twistN (n : ℕ) : (self A N).X.Modules :=
  twistingSheaf (ProjSpace.grading A N) (n : ℤ)

variable (A) in

def stdFrame (j : Fin (N + 1)) (n : ℕ) :
    ((preMod (self A N).X).obj (twistN A N n)).obj (op (ProjSpace.stdOpen A N j)) :=
  ProjTwist.upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)

theorem isBasisOn_frame (j : Fin (N + 1)) (n : ℕ) :
    IsBasisOn ((preMod (self A N).X).obj (twistN A N n)) (ProjSpace.stdOpen A N j) (stdFrame A j n) :=
  ProjTwist.isBasisOn_upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)

def fsFrameCoord (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ) :
    (self A N).Fibre (twistN A N n) x ≃ₗ[ℂ] ℂ :=
  fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x (rep_chartIndex_ne_zero x.1))
    (isBasisOn_frame (A := A) (CP.chartIndex x.1) n)

def fsFibreNorm (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ)
    (s : (self A N).Fibre (twistN A N n) x) : ℝ :=
  ‖fsFrameCoord n ρ x s‖ * ‖x.1.rep (CP.chartIndex x.1)‖ ^ n / norm2 x.1.rep ^ n

theorem fsFibreNorm_smul (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ) (c : ℂ)
    (s : (self A N).Fibre (twistN A N n) x) :
    fsFibreNorm n ρ x (c • s) = ‖c‖ * fsFibreNorm n ρ x s := by
  rw [fsFibreNorm, fsFibreNorm, LinearEquiv.map_smul, smul_eq_mul, norm_mul]
  ring

theorem fsFibreNorm_pos (n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ)
    (s : (self A N).Fibre (twistN A N n) x) (hs : s ≠ 0) : 0 < fsFibreNorm n ρ x s := by
  have h1 : 0 < ‖fsFrameCoord n ρ x s‖ :=
    norm_pos_iff.mpr fun h => hs ((fsFrameCoord n ρ x).map_eq_zero_iff.mp h)
  have h2 := norm_pos_iff.mpr (rep_chartIndex_ne_zero x.1)
  have h3 := euclideanNorm_pos x.1.rep_nonzero
  unfold fsFibreNorm
  positivity

def polyFun (P : MvPolynomial (Fin (N + 1)) A) (U : Opens (ProjectiveSpectrum.top (ProjSpace.grading A N))) :
    ∀ x : U, ProjTwist.Loc (ProjSpace.grading A N) x.1 :=
  fun _ => Localization.mk P 1

lemma isLocallyFraction_polyFun {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) (U : Opens (ProjectiveSpectrum.top (ProjSpace.grading A N))) :
    (ProjTwist.isLocallyFraction (ProjSpace.grading A N) (n : ℤ)).pred (polyFun P U) := fun x =>
  ⟨U, x.2, 𝟙 _, 0, n, by simp, P, 1, hP, SetLike.GradedOne.one_mem,
    fun y h => y.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), fun _ => rfl⟩

def polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n) :
    (self A N).H0 (twistN A N n) :=
  ProjTwist.mkSection (polyFun P ⊤) (isLocallyFraction_polyFun hP ⊤)

end ProjScheme

namespace SectionsLatticeFS

open ProjScheme

def PNFlat.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ), Flat (self A N).toBase

def PNReduced.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsReduced A] (N : ℕ), IsReduced (self A N).X

def FSContinuousFrame.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (U : (self A N).X.Opens)
    (e : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)),
    IsBasisOn ((preMod (self A N).X).obj (twistN A N n)) U e →
      Continuous fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} =>
        fsFibreNorm n ρ y.1 ((self A N).sectionValue y.1 y.2 e)

def FSNormConj.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (U : (self A N).X.Opens)
    (s : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)) (x : (self A N).complexPoints ρ)
    (hx : (self A N).point x ∈ U) (hx' : (self A N).point ((self A N).conjPoint ρ x) ∈ U),
      fsFibreNorm n ((starRingEnd ℂ).comp ρ) ((self A N).conjPoint ρ x)
          ((self A N).sectionValue _ hx' s) =
        fsFibreNorm n ρ x ((self A N).sectionValue x hx s)

def FSFullSupport.Statement : Prop :=
  ∀ (N : ℕ) (U : Set (CP N)), IsOpen U → U.Nonempty → 0 < CP.fsMeasure N U

def FSConjInvariant.Statement : Prop :=
  ∀ N : ℕ, (CP.fsMeasure N).map CP.conj = CP.fsMeasure N

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

variable {A : Type u} [CommRing A] {N : ℕ}

def fsMetric (hf : FSContinuousFrame.Statement.{u}) (hc : FSNormConj.Statement.{u}) (n : ℕ) :
    (self A N).ContinuousMetric (twistN A N n) where
  norm ρ x s := fsFibreNorm n ρ x s
  norm_smul ρ x c s := fsFibreNorm_smul n ρ x c s
  norm_pos ρ x s hs := fsFibreNorm_pos n ρ x s hs
  continuous_frame ρ U e he := hf A N n ρ U e he
  norm_conj ρ U s x hx hx' := hc A N n ρ U s x hx hx'

variable (K : Type) [Field K] [NumberField K]

variable {K}

end ProjScheme

namespace SectionsLatticeFS

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

end ProjScheme

end

end GroundTheory.Heights₂.Heights
