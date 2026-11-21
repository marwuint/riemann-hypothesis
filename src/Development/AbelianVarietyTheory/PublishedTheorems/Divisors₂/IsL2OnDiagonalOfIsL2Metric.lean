import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormWithPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points (PtsOver)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm (IsRegVar BottChern ArChow hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (om0)
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.TorsionForm

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
  {g D : ℕ}

def cot (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (W : A.left.Opens) (f : Γ(A.left, W)) (v : V D) :
    Fin g → ℂ := fun a => fderiv ℂ (fun z => ev (A.hom ≫ p) σ W f (ex (v, z))) 0 (Pi.single a 1)

def IsPeriodChart [GrpObj A] (h : VMetric p (omega A) g) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  IsPeriodMap c.e.target τ ∧ IsHolTo (cov c.e.target g) (fun P => (ex P).1) ∧ ∀ v ∈ c.e.target,
    (∀ z, (ex (v, z)).1 ≫ A.hom = (c.e.symm v).1) ∧
    (∀ z w, ∀ x y : Over.mk (c.e.symm v).1 ⟶ A, x.left = (ex (v, z)).1 → y.left = (ex (v, w)).1 →
      (x * y).left = (ex (v, z + w)).1) ∧
    (∀ x : Over.mk (c.e.symm v).1 ⟶ A, ∃ z, x.left = (ex (v, z)).1) ∧
    (∀ z, (ex (v, z)).1 = (c.e.symm v).1 ≫ unitSec A ↔ ∃ l ∈ stdLat g, z = per (τ v) l) ∧
    ∀ (U : S.Opens) (W : A.left.Opens) (hU : U ≤ unitSec A ⁻¹ᵁ W) (f f' : Γ(A.left, W)),
      c.e.symm v ∈ ptsIn p σ U → (h.met σ).form (dUnit A hU f) (dUnit A hU f') (c.e.symm v) =
        HermFrame.form ((2 : ℂ) • imPart τ v) (cot ex W f v) (cot ex W f' v)

def IsFramed (L : HermLB (A.hom ≫ p)) (B : Set (V D)) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (j : Fl g → Pt (V D) g → ℂ) (m : Pt (V D) g → ℝ) : Prop :=
  ∃ fr : L.B.ι → Pt (V D) g → ℂ, ∀ i,
    DifferentiableOn ℂ (fr i) (cov B g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) ∧
    ∀ P ∈ cov B g, ex P ∈ ptsIn _ σ (L.B.U i) → fr i P ≠ 0 ∧
      (∀ i', ex P ∈ ptsIn _ σ (L.B.U i') → fr i P = gv _ σ L.B i i' (ex P) * fr i' P) ∧
      m P = ‖fr i P‖ ^ 2 * Real.exp (-(L.φ σ).φ i (ex P)) ∧
      ∀ l ∈ stdLat g, fr i P = j l P * fr i (transl τ l P)

section Global

variable {D' r : ℕ}

def IsUnifChart (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  IsPeriodMap c.e.target τ ∧ IsHolTo (cov c.e.target g) (fun P => (ex P).1) ∧ ∀ v ∈ c.e.target,
    (∀ z, (ex (v, z)).1 ≫ A.hom = (c.e.symm v).1) ∧
    (∀ y : CxPts (A.hom ≫ p) σ, y.1 ≫ A.hom = (c.e.symm v).1 → ∃ z, ex (v, z) = y) ∧
    ∀ z w, ex (v, z) = ex (v, w) ↔ ∃ l ∈ stdLat g, z = w + per (τ v) l

def IsFlatOn (h' : IsRegVar (A.hom ≫ p) D') (Ω : (h'.atlas σ).Fld) (B : Set (V D))
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ P ∈ cov B g, ∀ x : (h'.atlas σ).Pt, x.pt = ex P → ∀ v w : Pt (V D) g,
    eval₂ (Ω x) (fderiv ℂ (x.ch ∘ ex) P v) (fderiv ℂ (x.ch ∘ ex) P w) = om0 τ P ![v, w]

def fibForm (h : IsRegVar p D) (h' : IsRegVar (A.hom ≫ p) D') (Ω₀ : (h'.atlas σ).Fld) (κ : (h.atlas σ).Fld) :
    (h'.atlas σ).Fld :=
  Ω₀ + (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map A.hom rfl _) κ

variable (g) in

def IsFlatFibration (h : IsRegVar p D) (h' : IsRegVar (A.hom ≫ p) D') (Ω₀ : (h'.atlas σ).Fld)
    (κ : (h.atlas σ).Fld) : Prop :=
  (h.atlas σ).IsRealForm 1 κ ∧ (h'.atlas σ).IsRealForm 1 (fibForm h h' Ω₀ κ) ∧
    (h'.atlas σ).del (fibForm h h' Ω₀ κ) = 0 ∧ (h'.atlas σ).dbar (fibForm h h' Ω₀ κ) = 0 ∧
    ∀ y : CxPts p σ, ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ),
      y ∈ c.e.source ∧ IsUnifChart c τ ex ∧ IsFlatOn h' Ω₀ c.e.target τ ex

def cotAt (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (W : A.left.Opens) (f : Γ(A.left, W)) (P : Pt (V D) g) :
    Fin g → ℂ := fun a => fderiv ℂ (fun z => ev (A.hom ≫ p) σ W f (ex (P.1, z))) P.2 (Pi.single a 1)

def IsFibreMetric (m : VMetric (A.hom ≫ p) (relCot A.hom) g) (B : Set (V D))
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ P ∈ cov B g, ∀ (W : A.left.Opens) (f f' : Γ(A.left, W)), ex P ∈ ptsIn _ σ W →
    (m.met σ).form (dRel A.hom W f) (dRel A.hom W f') (ex P) =
      HermFrame.form ((2 : ℂ) • imPart τ P.1) (cotAt ex W f P) (cotAt ex W f' P)

def IsL2Metric (L : HermLB (A.hom ≫ p)) (M : HermVB p r)
    (ψ : M.E ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ v ∈ c.e.target, ∀ (U : S.Opens) (s t : Γ(M.E, U)), c.e.symm v ∈ ptsIn p σ U →
    (M.h.met σ).form s t (c.e.symm v) = ((2 * π : ℂ) ^ g)⁻¹ *
      ∫ x in Icc (0 : Fl g) 1, ((VMetric.ofLB L).met σ).form (V := A.hom ⁻¹ᵁ U)
        (ψ.hom.app U s) (ψ.hom.app U t) (ex (v, per (τ v) x))

variable (g) in

def IsTorsionOn (h : IsRegVar p D) (h' : IsRegVar (A.hom ≫ p) D') (Ω₀ : (h'.atlas σ).Fld)
    (κ : (h.atlas σ).Fld) (L : HermLB (A.hom ≫ p)) (T : ℕ → (h.atlas σ).Fld) : Prop :=
  (∀ i, (h.atlas σ).IsRealForm i (T i)) ∧ ∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (j : Fl g → Pt (V D) g → ℂ) (m : Pt (V D) g → ℝ),
    IsUnifChart c τ ex → IsFlatOn h' Ω₀ c.e.target τ ex → IsFramed L c.e.target τ ex j m →
    ∀ v ∈ c.e.target, IsTorsionFormWith τ (stdLat g) j m coordVec v (hermMat ((h.atlas σ).loc κ c v))
      ((bas D).repr ((h.atlas σ).loc (∑ i ∈ Finset.range (D + 1), T i) c v))

end Global

end GlobalTheory.TorsionForm

namespace GlobalTheory.Published

open GlobalTheory.TorsionForm MvPolynomial

def BismutKoehlerTorsion : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → (∀ b ∈ B, IsAcyclicAt τ M j h b) → ∀ β : Fin n → E,
    ∃ T : E → Ext (n + n), ContDiffOn ℝ ∞ T B ∧ ∀ b ∈ B,
      (∀ T', IsTorsionForm τ M j h β b T' ↔ T' = T b) ∧
      (∀ I, (I.filter (·.val < n)).card ≠ (I.filter (n ≤ ·.val)).card → T b I = 0) ∧
      (T b ∅).im = 0 ∧
      ∀ i l : Fin n, T b {l.castAdd n, i.natAdd n} = -star (T b {i.castAdd n, l.natAdd n})

def BismutKoehlerTorsionWith : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → (∀ b ∈ B, IsAcyclicAt τ M j h b) →
    ∀ κ : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ, IsClosedHerm B κ → ∀ β : Fin n → E,
    ∃ T : E → Ext (n + n), ContDiffOn ℝ ∞ T B ∧ ∀ b ∈ B,
      (∀ T', IsTorsionFormWith τ M j h β b (of fun i l => κ b (β i) (β l)) T' ↔ T' = T b) ∧
      (∀ I, (I.filter (·.val < n)).card ≠ (I.filter (n ≤ ·.val)).card → T b I = 0) ∧
      (T b ∅).im = 0 ∧
      ∀ i l : Fin n, T b {l.castAdd n, i.natAdd n} = -star (T b {i.castAdd n, l.natAdd n})

def BismutKoehlerGlobal : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) (D' : ℕ)
    (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), SmoothOfRelativeDimension g A.hom →
    ∀ L : HermLB (A.hom ≫ p), IsRelAcyclic (A.hom ≫ p) A.hom L.B →
    ∀ (σ : k →+* ℂ) (Ω₀ : (h'.atlas σ).Fld) (κ : (h.atlas σ).Fld), IsFlatFibration g h h' Ω₀ κ →
    ∃ T, IsTorsionOn g h h' Ω₀ κ L T

def TorsionAnomaly : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) (D' : ℕ)
    (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), SmoothOfRelativeDimension g A.hom →
    ∀ L : HermLB (A.hom ≫ p), IsRelAcyclic (A.hom ≫ p) A.hom L.B →
    ∀ (σ : k →+* ℂ) (Ω₀ : (h'.atlas σ).Fld) (κ κ' : (h.atlas σ).Fld), IsFlatFibration g h h' Ω₀ κ →
    IsFlatFibration g h h' Ω₀ κ' → ∀ T T', IsTorsionOn g h h' Ω₀ κ L T → IsTorsionOn g h h' Ω₀ κ' L T' →
    ∀ i, (h.atlas σ).IsExact (T i - T' i)

def GilletRoesslerSoule : Prop :=
  ∃ B : BottChern, ∀ (k : Type) [CommRing k], ∃ (C : ArChow B k) (P : C.Push),
    ∀ (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) (D' : ℕ)
      (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), SmoothOfRelativeDimension g A.hom →
    ∀ (hs : IsGenSmooth (A.hom ≫ p) A.hom) (Ω₀ : h'.Fld) (κ : h.Fld),
      (∀ σ, IsFlatFibration g h h' (Ω₀ σ) (κ σ)) → h'.IsArForm 1 (fun σ => fibForm h h' (Ω₀ σ) (κ σ)) →
      (∀ σ x, (hermMat (fibForm h h' (Ω₀ σ) (κ σ) x)).PosDef) →
    ∀ (m : VMetric (A.hom ≫ p) (relCot A.hom) g) (H : m.IsCInf) (L : HermLB (A.hom ≫ p)),
      IsRelAcyclic (A.hom ≫ p) A.hom L.B →
    ∀ (r : ℕ) (M : HermVB p r) (ψ : M.E ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)),
      (∀ σ (y : CxPts p σ), ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
        (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsUnifChart c τ ex ∧
          IsFlatOn h' (Ω₀ σ) c.e.target τ ex ∧ IsFibreMetric m c.e.target τ ex ∧ IsL2Metric L M ψ c τ ex) →
    ∃ T T' : ℕ → h.Fld, (∀ σ, IsTorsionOn g h h' (Ω₀ σ) (κ σ) L fun i => T i σ) ∧
      (∀ i, h.IsArForm i (T' i) ∧ ∀ σ, (h.atlas σ).IsExact (T i σ - T' i σ)) ∧
      (C.ring h).ch M - (C.ring h).a (∑ i ∈ Finset.range (D + 1), T' i) =
        P.push h h' A.hom rfl hs ((C.ring h').td (HermVB.dual ⟨_, m, H⟩) *
          (1 - (C.ring h').a ((C.ring h').rForm (HermVB.dual ⟨_, m, H⟩))) * (C.ring h').ch (.ofLB L))

def AmpleVanishing : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic A.hom A.hom L

def ArithRiemannRoch : Prop :=
  BismutKoehlerTorsion ∧ BismutKoehlerTorsionWith ∧ BismutKoehlerGlobal ∧ TorsionAnomaly ∧ GilletRoesslerSoule ∧
    AmpleVanishing

end GlobalTheory.Published
