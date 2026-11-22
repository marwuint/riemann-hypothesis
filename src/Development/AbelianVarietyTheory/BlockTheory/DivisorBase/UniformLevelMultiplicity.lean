import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Side (D : D7) (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E x)) =
    D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E x))

abbrev Emb (D : D7) : Type := {σ : D.what₂.LL →+* ℂ // Side D σ}

def SitsAt (D : D7) (σ : D.what₂.LL →+* ℂ) (τ τ' : D.what₂.Tau) : Prop :=
  ∃ t : D.host.E →+* D.what₂.LL, D.what₂.embLL.comp t = tauE D τ ∧ σ.comp t = tauE D τ'

def IsConjPar (D : D7) (j : ℕ) (σ : D.what₂.LL →+* ℂ) (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ', ∃ τ, SitsAt D σ τ τ' ∧ S τ' = parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)) τ

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def IsCover (V : HSp D) {G0 : Type} [Group G0] (Lift : G0 → GA D V → Prop) : Prop :=
  (∀ κ, κ ∈ levSet V 1 ↔ ∃ g, Lift g κ) ∧ (∀ g, ∃ κ, Lift g κ) ∧
    (∀ g g' κ, Lift g κ → Lift g' κ → g = g') ∧
    (∀ g g' κ κ', Lift g κ → Lift g' κ' → Lift (g * g') (κ * κ')) ∧
    ∀ κ, Lift 1 κ ↔ κ ∈ levSet V (D.host.g 0 * D.host.g 1)

abbrev MultK (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) : Submodule ℂ (MMap M) :=
  Mult θ M (levSet V (D.host.g 0 * D.host.g 1)) (fun _ => 1)

def UnifCl (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] {G0 : Type} [Group G0]
    (Lift : G0 → GA D V → Prop) (ρ : G0 →* (WL →ₗ[D.what₂.LL] WL)) (χ : G0 →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ)
    (J : WL →ₛₗ[σ] MMap M) : Prop :=
  (∀ (n : ℕ) (b : Fin n → WL), LinearIndependent D.what₂.LL b → LinearIndependent ℂ (fun i => J (b i))) ∧
    Submodule.span ℂ (Set.range J) = MultK θ M ∧
    ∀ g κ, Lift g κ → ∀ (x : WL) (v : M.Vec) (h : GA D V),
      J (ρ g x) v h = σ ((χ g : D.what₂.LLˣ) : D.what₂.LL) * J x v (h * κ)

def IsAnSide (j : ℕ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : Emb D → HSp D)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ, DSModel (V σ) (S σ)) {G0 : Type} [Group G0]
    (Lift : ∀ σ, G0 → GA D (V σ) → Prop) {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, AddCommGroup (W σ)]
    [∀ σ, Module ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ)) : Prop :=
  InR D j ∧ IsInfFam θ ∧ ∀ σ : Emb D, V σ = D.sp.W j ∧ IsConjPar D j σ.1 (S σ) ∧ IsCover (V σ) (Lift σ) ∧
    Function.Injective (ev σ) ∧ LinearMap.range (ev σ) = MultK θ (M σ)

def UnifEvery (j : ℕ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : Emb D → HSp D)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ, DSModel (V σ) (S σ)) {G0 : Type} [Group G0]
    (Lift : ∀ σ, G0 → GA D (V σ) → Prop) {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) : Prop :=
  IsAnSide j θ V S M Lift ev ∧ ∀ σ : Emb D, UnifCl θ (M σ) (Lift σ) A.ρ A.chi σ.1 ((ev σ).comp (A.j σ.1))

variable (T : CoreJ D) (j : ℕ)

variable [Algebra T.Q.c.F D.what₂.LL]

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
