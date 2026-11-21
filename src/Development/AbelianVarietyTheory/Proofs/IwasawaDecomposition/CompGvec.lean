import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

section Lin

abbrev GVar (m a k b : ℕ) : Type :=
  {il : Fin m × Fin m // a ≤ (il.2 : ℕ) ∧ (il.2 : ℕ) < k ∧ k ≤ (il.1 : ℕ) ∧ (il.1 : ℕ) < b}

abbrev GPm (m a b : ℕ) : Type := {w : Equiv.Perm (Fin m) // ∀ i : Fin m, (i : ℕ) < a ∨ b ≤ (i : ℕ) → w i = i}

variable {S : Type} [CommRing S] {m a k b N : ℕ}

def gcell (x : GVar m a k b → S) (i l : Fin m) : S :=
  if h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b then x ⟨(i, l), h⟩ else if i = l then 1 else 0

def gvec {Q : Type} [AddCommGroup Q] [Module S Q] (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) : Fin m → Q :=
  fun l => ∑ i, gcell x i l • c (w.1 i)

variable (a b) in

def gxi (hk : k ≤ m) (c : Fin m → Fin (N + 1) → S) (w : GPm m a b) :
    Fin (plN N k + 1) → MvPolynomial (GVar m a k b) S :=
  plk (gvec (fun l => (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) ∘ c l) w
    (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S)) (Fin.castLE hk)

structure Cells {R : Type} [CommRing R] (ρ : R →+* S) {J : Type} (ξ : J → Fin (N + 1) → S) (ℓ : J → Fin (N + 1) → R) :
    Prop where
  one : ∀ j, ∑ q, ρ (ℓ j q) * ξ j q = 1
  gen : ∀ j, Function.Surjective (MvPolynomial.eval₂Hom ρ (ξ j))
  ovl : ∀ (K : Type) [Field K] (j j' : J) (ψ' : S →+* K), ∑ q, ψ' (ρ (ℓ j q)) * ψ' (ξ j' q) ≠ 0 →
    ∃ (ψ : S →+* K) (u : Kˣ), ψ.comp ρ = ψ'.comp ρ ∧ ψ' ∘ ξ j' = (u : K) • (ψ ∘ ξ j)
  lin : ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → J) (e : T → R),
    ∀ j', ξ j' q = ∑ t, ρ (e t) * ∑ q', ρ (ℓ (jj t) q') * ξ j' q'

end Lin

section Geom

variable {O : Type} [CommRing O] {Z Z' : Scheme.{0}}

def Lifts (s : Z ⟶ Sp O) {N : ℕ} (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (z : Sp R ⟶ Z) (y₀ : Sp R ⟶ PSpace O N) (y : Sp K ⟶ Z'), y₀ ≫ PSpace.str O N = z ≫ s →
    y ≫ f = spMap (algebraMap R K) ≫ z → y ≫ q = spMap (algebraMap R K) ≫ y₀ →
    ∃ z' : Sp R ⟶ Z', spMap (algebraMap R K) ≫ z' = y

structure CellCl (s : Z ⟶ Sp O) (ch : Charts Z) (g : ∀ a, O →+* ch.R a) {V J : Type} {N : ℕ}
    (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N)
    (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')) : Prop where
  proj : IsProjOver (f ≫ s)
  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z'
  flat : Flat (f ≫ s)
  ovr : q ≫ PSpace.str O N = f ≫ s
  opn : ∀ a j, IsOpenImmersion (κ a j)
  sq : ∀ a j, κ a j ≫ f = spMap (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) ≫ ch.χ a
  pl : ∀ a j, ∃ hv, κ a j ≫ q = pt ((MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)).comp (g a)) (ξ a j) hv
  cover : ⋃ a, ⋃ j, Set.range (κ a j) = f ⁻¹' ch.carrier
  dense : Dense (f ⁻¹' ch.carrier)
  inj : ∀ (K : Type) [Field K] (w w' : Sp K ⟶ Z'), Set.range (w ≫ f) ⊆ ch.carrier → w ≫ f = w' ≫ f → w ≫ q = w' ≫ q →
    w = w'
  lift : Lifts s f q

variable {C : Coc Z} {N k : ℕ} (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k))

def Car {K : Type} [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K) : Prop :=
  ∃ (g : O →+* K) (hv : _), w ≫ q = pt g (plk (fun l => ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (ξ l)) id) hv

end Geom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Crd

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}

structure LCrd (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) : Type 1 where
  C : Coc X
  N : ℕ
  Em : C.Emb N
  crd : ∀ (α : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X), ⊤ ≤ z ⁻¹ᵁ C.B α →
    (TanM (z ≫ π) M.t.G →ₗ[S] (Fin (C.n α) → S))
  tr : ∀ (α β : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β)
    (v : TanM (z ≫ π) M.t.G), (C.tr α β z hα hβ).mulVec (crd β S z hβ v) = crd α S z hα v
  bc : ∀ (α : C.A) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ X) (z' : Sp S' ⟶ X)
    (_ : spMap φ ≫ z = z') (h : ⊤ ≤ z ⁻¹ᵁ C.B α) (h' : ⊤ ≤ z' ⁻¹ᵁ C.B α) (e : spMap φ ≫ z ≫ π = z' ≫ π)
    (v : TanM (z ≫ π) M.t.G), crd α S' z' h' (tanPull φ e v) = φ ∘ crd α S z h v
  inj : ∀ (α : C.A) (K : Type) [Field K] (z : Sp K ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ C.B α),
    Set.range z ⊆ π ⁻¹' Set.range M.j → Function.Injective (crd α K z h)

variable {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

def LCrd.emb (D : LCrd M π) (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α)
    (v : TanM (z ≫ π) M.t.G) : Fin (D.N + 1) → S := ((D.Em.A α).map (ev z _ h)).mulVec (D.crd α S z h v)

end Crd

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end GlobalTheory.GrCl
