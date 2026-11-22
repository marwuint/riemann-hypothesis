import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

structure ManIs {e : ℕ} (M : Man e) (Y : Var F) : Type where

  ε : Fin (M.n + 1) ≃ (F →+* ℂ)

  pt : ∀ a, M.X a ≃ₜ Pts Y (ε a)

  alg : ∀ a j, ∃ c : AlgChart Y.str (ε a) e, (M.A a).chart j = (pt a).transOpenPartialHomeomorph c.finChart

instance compactSpace_pts (σ : F →+* ℂ) : CompactSpace (Pts Y σ) := CxPts.compactSpace σ Y.isProjOver

section Norms

variable {σ : F →+* ℂ} {Δ : Y.Dv}

abbrev genAt (Δ : Y.Dv) (x : Y.X) : Y.Fn := ((eqn Δ x)⁻¹ : Y.Fnˣ)

def lnN (m : C.Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ) : ℝ := Real.log (C.pn Y σ Δ m (C.cx Y σ f) y) / 2

def lnRatio (m m' : C.Met Y σ Δ) (y : Pts Y σ) : ℝ :=
  lnN m (genAt Δ (under y)) y - lnN m' (genAt Δ (under y)) y

def PosAt (m : C.Met Y σ Δ) (y : Pts Y σ) : Prop := 0 < C.pn Y σ Δ m (C.cx Y σ (genAt Δ (under y))) y

def IsPot {X : Type} [TopologicalSpace X] (h : X → Pts Y σ) (m : C.Met Y σ Δ) (P : LocPot X) : Prop :=
  ∀ x, ∃ f : Y.Fn, ∀ y ∈ P.U x, Δ.GeneratesAt (under (h y)) f ∧ PosAt m (h y) ∧ P.φ x y = -lnN m f (h y)

end Norms

def ManIs.FormOf {e : ℕ} {M : Man e} (I : ManIs M Y) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m : ∀ i σ, C.Met Y σ (Δ i)) (t : ι → ℝ) (P : M.Pot) : Prop :=
  ∀ a, ∃ Q : ι → LocPot (M.X a), (∀ i, IsPot (I.pt a) (m i _) (Q i) ∧ IsPotential (M.A a) (Q i)) ∧
    ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) (P a) j y w = ∑ i, t i * leviAt (M.A a) (Q i) j y w

def ManIs.Lists {e : ℕ} {M : Man e} (I : ManIs M Y) (x : Y.X) {d : ℕ} (z : ∀ a, Fin d → M.X a) : Prop :=
  ∀ a, Function.Injective (z a) ∧ Set.range (z a) = {w | under (I.pt a w) = x}

structure Cover (Y : Var F) : Type 1 where

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  G : Scheme.{0}
  [intG : IsIntegral G]

  j : G ⟶ X

  π : G ⟶ Y.X

  pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))
  [fin : IsFinite π]
  [surj : Surjective π]

  φ : Y.Fn →+* G.functionField

  φ_spec : G.fromSpecStalk (genericPoint G) ≫ π = spMap φ ≫ Y.X.fromSpecStalk (genericPoint Y.X)

attribute [instance] Cover.int Cover.intG Cover.fin Cover.surj

namespace Cover

variable (V : Cover Y)

def deg : ℕ := V.π.residueDegree (genericPoint V.G)

def ν : ℝ := (Module.finrank ℚ F : ℝ) * V.deg

theorem deg_pos : 0 < V.deg := by
  let := (V.π.residueFieldMap (genericPoint V.G)).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π (genericPoint V.G))) (V.G.residueField (genericPoint V.G)) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

def ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : Cover Y where
  X := M.X
  int := M.ar.isIntegral
  p := M.p
  ar := M.ar
  normal := h
  G := Y.X
  j := M.j
  π := 𝟙 _
  pb := by simpa using M.pb
  φ := RingHom.id _
  φ_spec := (Category.comp_id _).trans ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm

def Induces (A : Adl C Y) (L : HermLB V.p) (k : ℕ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) ^ k * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (V.φ (genAt A.D (under y)) ^ k * (r i : V.G.functionField)) z‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      k * A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r i : V.G.functionField))))

def IsDown {e : ℕ} {M : Man e} (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1))
    (π : ∀ σ, CxPts V.p σ → M.X (ε σ)) : Prop :=
  ∀ σ, (I.ε (ε σ)).comp (algebraMap (𝓞 F) F) = σ ∧
    ∀ z, ∃ w : Sp ℂ ⟶ V.G, w ≫ V.j = z.1 ∧ w ≫ V.π = (I.pt _ (π σ z)).1

end Cover

end GlobalTheory.Mean4O
