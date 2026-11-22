import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.DeRham (spOver)
open GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateDef

section Notions

variable {S S₀ : Scheme.{0}} {A B : Over S} {A₀ B₀ : Over S₀}

def IsPairRed (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left) (P : LB (A ⊗ B).left) (P₀ : LB (A₀ ⊗ B₀).left) :
    Prop :=
  ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
    l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j ∧ LBIso P₀ (P.pull l)

abbrev polBundle (P : LB (A ⊗ B).left) (lam : A ⟶ B) : LB (A ⊗ A).left := ev P (fst A A) (snd A A ≫ lam)

end Notions

section Clauses

variable (p : ℕ) [Fact p.Prime] (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀]

abbrev red : Sp R₀ ⟶ Sp R := spMap (algebraMap R R₀)

def HasTower : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∃ G : PDivGroup p R, Nonempty (G.TorsionTower A) ∧
      ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → G.height = 2 * g

def DualTower : Prop :=
  ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B →
    IsDual A B P → ∀ (G H : PDivGroup p R) (t : G.TorsionTower A) (u : H.TorsionTower B),
      ∃ w : G ⟶ H.dual, IsWeilHom t u P w ∧ IsIso w

def LiftObj : Prop :=
  ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (G : PDivGroup p R) (t₀ : (G.baseChange R₀).TorsionTower A₀),
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (red R R₀) i)
        (t : G.TorsionTower A), IsAbelianScheme A ∧ t.baseChange h = t₀ ∧
        ∀ g : ℕ, SmoothOfRelativeDimension g A₀.hom → SmoothOfRelativeDimension g A.hom

def LiftHom : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (red R R₀) i), IsAbelianScheme A →
  ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] (j : B₀.left ⟶ B.left)
    (k : IsGrpPullback B₀ B (red R R₀) j), IsAbelianScheme B →
  ∀ (G H : PDivGroup p R) (t : G.TorsionTower A) (u : H.TorsionTower B) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : G ⟶ H),
    PDivGroup.baseChangeMap R₀ φ = (t.baseChange h).map (u.baseChange k) f₀ →
      ∃! f : A ⟶ B, ∃ _ : IsMonHom f, i ≫ f.left = f₀.left ≫ j ∧ t.map u f = φ

def RigidAbelian : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (red R R₀) i → IsAbelianScheme A →
  ∀ (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
  ∀ f f' : A ⟶ B, IsMonHom f → IsMonHom f' → i ≫ f.left = i ≫ f'.left → f = f'

def RigidPDiv : Prop :=
  ∀ (G H : PDivGroup p R) (φ φ' : G ⟶ H), PDivGroup.baseChangeMap R₀ φ = PDivGroup.baseChangeMap R₀ φ' → φ = φ'

def LiftAct : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] [IsCommMonObj A₀]
    (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (red R R₀) i), IsAbelianScheme A →
  ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (Λ : Type) [Ring Λ] (a₀ : RingAct A₀ Λ) (ρ : Action Λ G),
    (∀ x, PDivGroup.baseChangeMap R₀ (ρ x : G ⟶ G) = ((t.baseChange h).ringAct a₀ x : _ ⟶ _)) →
      ∃! a : RingAct A Λ, (∀ x, i ≫ (a.act x).left = (a₀.act x).left ≫ i) ∧ t.ringAct a = ρ

def LiftDual : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (red R R₀) i → IsAbelianScheme A →
  ∀ (B₀ : Over (Sp R₀)) [GrpObj B₀] (P₀ : LB (A₀ ⊗ B₀).left), IsAbelianScheme B₀ → IsDual A₀ B₀ P₀ →
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (j : B₀.left ⟶ B.left) (P : LB (A ⊗ B).left),
      IsAbelianScheme B ∧ IsGrpPullback B₀ B (red R R₀) j ∧ IsDual A B P ∧ IsPairRed i j P P₀

def LiftPol : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (red R R₀) i), IsAbelianScheme A →
  ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] (j : B₀.left ⟶ B.left),
    IsGrpPullback B₀ B (red R R₀) j → IsAbelianScheme B →
  ∀ (P : LB (A ⊗ B).left) (P₀ : LB (A₀ ⊗ B₀).left), IsDual A B P → IsDual A₀ B₀ P₀ → IsPairRed i j P P₀ →
  ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (lam₀ : A₀ ⟶ B₀) (ψ : G ⟶ G.dual), IsPolarisation A₀ B₀ P₀ lam₀ →
    IsWeilHom (t.baseChange h) (t.baseChange h) (polBundle P₀ lam₀)
      (PDivGroup.baseChangeMap R₀ ψ ≫ (dualBaseChange R₀ G).inv) →
      ∃! lam : A ⟶ B, IsPolarisation A B P lam ∧ i ≫ lam.left = lam₀.left ≫ j ∧ IsWeilHom t t (polBundle P lam) ψ

def RigidBundle : Prop :=
  ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (red R R₀) i → IsAbelianScheme A →
  ∀ (C : Over (Sp R)) [GrpObj C] (C₀ : Over (Sp R₀)) [GrpObj C₀] (j : C₀.left ⟶ C.left),
    IsGrpPullback C₀ C (red R R₀) j → IsAbelianScheme C →
  ∀ (Q Q' : LB (A ⊗ C).left) (Q₀ : LB (A₀ ⊗ C₀).left), Q.IsLB → Q'.IsLB → Q₀.IsLB →
    IsAdditive Q → IsAdditive (swap Q) → IsAdditive Q' → IsAdditive (swap Q') →
    IsPairRed i j Q Q₀ → IsPairRed i j Q' Q₀ → LBIso Q Q'

def At : Prop :=
  HasTower p R ∧ DualTower p R ∧ LiftObj p R R₀ ∧ LiftHom p R R₀ ∧ RigidAbelian R R₀ ∧ RigidPDiv p R R₀ ∧
    LiftAct p R R₀ ∧ LiftDual R R₀ ∧ LiftPol p R R₀ ∧ RigidBundle R R₀

end Clauses

section Consequences

variable {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]

theorem At.exists_lift (H : At p R R₀) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] [IsCommMonObj A₀]
    (hA₀ : IsAbelianScheme A₀) (hB₀ : IsAbelianScheme B₀) {P₀ : LB (A₀ ⊗ B₀).left} (hP₀ : IsDual A₀ B₀ P₀)
    {Λ : Type} [Ring Λ] (a₀ : RingAct A₀ Λ) {lam₀ : A₀ ⟶ B₀} (hl : IsPolarisation A₀ B₀ P₀ lam₀)
    (G : PDivGroup p R) (t₀ : (G.baseChange R₀).TorsionTower A₀) (ρ : Action Λ G)
    (hρ : ∀ x, PDivGroup.baseChangeMap R₀ (ρ x : G ⟶ G) = (t₀.ringAct a₀ x : _ ⟶ _)) (ψ : G ⟶ G.dual)
    (hψ : IsWeilHom t₀ t₀ (polBundle P₀ lam₀) (PDivGroup.baseChangeMap R₀ ψ ≫ (dualBaseChange R₀ G).inv)) :
    ∃ (A B : Over (Sp R)) (_ : GrpObj A) (_ : GrpObj B) (_ : IsCommMonObj A) (i : A₀.left ⟶ A.left)
      (j : B₀.left ⟶ B.left) (h : IsGrpPullback A₀ A (red R R₀) i) (t : G.TorsionTower A) (P : LB (A ⊗ B).left)
      (a : RingAct A Λ) (lam : A ⟶ B), IsAbelianScheme A ∧ IsAbelianScheme B ∧ IsGrpPullback B₀ B (red R R₀) j ∧
      IsDual A B P ∧ IsPairRed i j P P₀ ∧ t.baseChange h = t₀ ∧
      (∀ x, i ≫ (a.act x).left = (a₀.act x).left ≫ i) ∧ t.ringAct a = ρ ∧
      IsPolarisation A B P lam ∧ i ≫ lam.left = lam₀.left ≫ j ∧ IsWeilHom t t (polBundle P lam) ψ := by
  obtain ⟨-, -, H₁, -, -, -, H₂, H₃, H₄, -⟩ := H
  obtain ⟨A, _, i, h, t, hA, rfl, -⟩ := H₁ A₀ hA₀ G t₀
  have := hA.comm
  obtain ⟨B, _, j, P, hB, k, hP, r⟩ := H₃ A A₀ i h hA B₀ P₀ hB₀ hP₀
  obtain ⟨a, ⟨a₁, a₂⟩, -⟩ := H₂ A A₀ i h hA G t Λ a₀ ρ hρ
  obtain ⟨lam, ⟨l₁, l₂, l₃⟩, -⟩ := H₄ A A₀ i h hA B B₀ j k hB P P₀ hP hP₀ r G t lam₀ ψ hl hψ
  exact ⟨A, B, _, _, this, i, j, h, t, P, a, lam, hA, hB, k, hP, r, rfl, a₁, a₂, l₁, l₂, l₃⟩

end Consequences

section Base

abbrev Zmod4 : Type := ZMod (2 ^ 2)

instance : Fact (1 < 2 ^ 2) := ⟨by norm_num⟩

instance : IsLocalRing Zmod4 := IsLocalRing.of_surjective' (PadicInt.toZModPow 2) (ZMod.ringHom_surjective _)

instance : Finite (IsLocalRing.ResidueField Zmod4) :=
  Finite.of_surjective _ (IsLocalRing.residue_surjective (R := Zmod4))

theorem two_mem : ((2 : ℕ) : Zmod4) ∈ IsLocalRing.maximalIdeal Zmod4 := fun h => by
  have h4 := h.mul h
  rw [show ((2 : ℕ) : Zmod4) * ((2 : ℕ) : Zmod4) = 0 by decide] at h4
  exact not_isUnit_zero h4

instance : CharP (IsLocalRing.ResidueField Zmod4) 2 := by
  refine (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 ?_
  rw [← map_natCast (IsLocalRing.residue Zmod4)]
  exact (IsLocalRing.residue_eq_zero_iff _).2 two_mem

end Base

section Elliptic

open GlobalTheory.WeierstrassCurve (ellPolAV)

def curve : _root_.WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩

instance : curve.IsElliptic := by
  refine ⟨?_⟩
  have e : curve.Δ = ((-27 : ℤ) : ℤ_[2]) := by
    simp [curve, _root_.WeierstrassCurve.Δ, _root_.WeierstrassCurve.b₂, _root_.WeierstrassCurve.b₄,
      _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈]
  rw [e, PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (-27)).1 h
  omega

variable (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀] [IsNoetherianRing R] [IsNoetherianRing R₀]

end Elliptic

end GlobalTheory.SerreTateDef
