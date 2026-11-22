import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section Sheaf

variable {O : Type} [CommRing O] {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

def resSec (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (A : X.Modules) (t : Γ((Scheme.Modules.pullback f).obj A, ⊤)) :
    Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) :=
  ((sqIso w).hom.app A).app ⊤ (QCoh.pullbackSections (spMap (algebraMap R K)) _ (V := ⊤) le_top t)

variable (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A B A' B' : X.Modules} {D : T.Modules}
  (a : (Scheme.Modules.pullback f₀).obj A ⟶ D) (b : D ⟶ (Scheme.Modules.pullback f₀).obj B)

variable {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

end Sheaf

section Tower

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

def IsWeilHom {𝒜 ℬ : PDivGroup p R} {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (t : 𝒜.TorsionTower A)
    (u : ℬ.TorsionTower B) (P : LB (A ⊗ B).left) (w : 𝒜 ⟶ ℬ.dual) : Prop :=
  ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ,
    Out.WeilIs (A ⊗ B) P ((p ^ n : ℕ) : ℤ) (T := SpAlg R (𝒜.A n ⊗[R] ℬ.A n))
      (CartesianMonoidalCategory.lift (spOver Algebra.TensorProduct.includeLeft ≫ t.y n) 1)
      (CartesianMonoidalCategory.lift 1 (spOver Algebra.TensorProduct.includeRight ≫ u.y n)) (unitOn U) ∧
    ∀ χ : CartierDual R (ℬ.A n), w.app n χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U.val)

variable [Fact p.Prime] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

variable [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

end Tower

end GlobalTheory.BadPt
