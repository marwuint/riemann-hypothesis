import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent unitOn)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta)
open ReciprocityTheory.ChartRestriction.G.Out (WeilIs)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R)

def IsConnecting (x : G.VecExt) (b : G.A 1) : Prop :=
  ∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
    G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b

variable {G}

end PDivGroup

namespace EpsWeil

variable {R : Type} [CommRing R] (D : Type) [CommRing D] [Algebra R D]

variable {D} in

def epsUnit (b : D) : (DualNumber D)ˣ where
  val := 1 + TrivSqZeroExt.inr b
  inv := 1 - TrivSqZeroExt.inr b
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

variable (R) in

def epsMap : DualNumber R →ₐ[R] DualNumber D :=
  DualNumber.lift ⟨(Algebra.ofId R _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

variable {D} {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def PairsTo (P : LB (A ⊗ B).left) (n : ℕ) (x : PDiv.SpAlg R D ⟶ A) (v : epsR R ⟶ B) (b : D) : Prop :=
  WeilIs (A ⊗ B) P (n : ℤ) (T := PDiv.SpAlg R (DualNumber D))
    (lift (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x) 1) (lift 1 (spOver (epsMap R D) ≫ v))
    (unitOn (epsUnit b))

end EpsWeil

namespace Published

namespace BarsottiTateDieudonne

def WittModule : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
      (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
      (red : ∀ G : PDivGroup p k,
        M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
      (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
        Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
        (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
      (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
        map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
      ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
        red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

def WeilCompatible {p : ℕ} [Fact p.Prime] (e : DeRhamVectorExtension.Family p) (s : ℤˣ) : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : (p : R) = 0) ⦃A B : Over (Sp R)⦄ [GrpObj A] [GrpObj B] ⦃g : ℕ⦄
    (hA : IsAbelianScheme A), IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ ⦃P : LB (A ⊗ B).left⦄, AbDual.IsDual A B P →
    ∀ ⦃φ : HdR A →ₗ[R] HdR B →ₗ[R] R⦄, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) ⦃h' : HdR B⦄ ⦃v : epsR R ⟶ B⦄, IsLieImage h' v →
    ∀ ⦃b : G.A 1⦄, EpsWeil.PairsTo P p (t.y 1) v b →
    ∀ ⦃c : primDR A⦄, (∀ h ∈ Fil A, φ h h' = h c) →
      G.IsConnecting (G.rigToExt (e (hR ▸ IsNilpotent.zero) hA t c)) (s • b)

def HodgeQuotient : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ (e : DeRhamVectorExtension.Family p) (s : ℤˣ),
    e.Natural ∧ e.Filtered ∧ e.Tangent ∧ WeilCompatible e s

end BarsottiTateDieudonne

def BarsottiTateDieudonne : Prop :=
  BarsottiTateDieudonne.WittModule ∧ BarsottiTateDieudonne.HodgeQuotient

namespace BarsottiTateDieudonne

end BarsottiTateDieudonne

end Published

end GlobalTheory
