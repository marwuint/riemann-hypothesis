import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw

namespace GlobalTheory.LocSW

section Group

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

def conjR : R ⊗[F] E →ₐ[R] R ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id R R) σ

@[simp] theorem conjR_tmul (r : R) (e : E) : conjR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := rfl

theorem conjR_eq_sigR (z : R ⊗[F] E) : conjR R σ z = sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_conjR {α β : Type} (M : Matrix α β (R ⊗[F] E)) : M.map (conjR R σ) = M.map (sigR R σ) :=
  Matrix.ext fun _ _ => conjR_eq_sigR R σ _

theorem UG_eq_HR (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : UG (conjR R σ) (JR R Q) = HR R σ Q := by
  have hJ : (JR (F := F) R Q)ᵀ = -JR R Q := by
    rw [JR_eq R hQ, StdUnn.blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
    change _ = (-Matrix.fromBlocks 0 1 (-1) 0).submatrix _ _
    rw [Matrix.fromBlocks_neg]
    simp
  ext g
  change (g.1)ᵀ * JR R Q * (g.1).map (conjR R σ) = JR R Q ↔ cT (sigR R σ) g.1 * JR R Q * g.1 = JR R Q
  rw [map_conjR, cT]
  constructor <;> intro h <;> have := congrArg Matrix.transpose h <;>
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, hJ] using this

def toUG (hQ : Q = StdUnn.blk4 0 1 (-1) 0) : HA R σ Q ≃* UG (conjR R σ) (JR R Q) :=
  MulEquiv.subgroupCongr (UG_eq_HR R σ hQ).symm

variable {R σ}

@[simp] theorem coe_toUG (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (g : HA R σ Q) :
    ((toUG R σ hQ g : GL (Fin (n + n)) (R ⊗[F] E)) : Matrix _ _ _) = matR R σ g := rfl

@[simp] theorem matR_toUG_symm (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (g : UG (conjR R σ) (JR R Q)) :
    matR R σ ((toUG R σ hQ).symm g) = ((g : GL (Fin (n + n)) (R ⊗[F] E)) : Matrix _ _ _) := rfl

end Group

section Finite

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (om : G →* Module.End ℂ V) (K : Subgroup G)

def coefMap (l : V →ₗ[ℂ] ℂ) : V →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun g => l ∘ₗ om g

variable {S om K}

@[simp] theorem coefMap_apply (l : V →ₗ[ℂ] ℂ) (φ : V) (g : G) : coefMap om l φ g = l (om g φ) := rfl

end Finite

section Model

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)]
  (σ : E →ₐ[F] E) {n m : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

abbrev LocDbx (JA : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (κ : Type) [Fintype κ] :
    Type := Darboux (symp (R := R) (conjR R σ) (-1) JA (JR R Q)) κ

variable {σ} {hQ : Q = StdUnn.blk4 0 1 (-1) 0} {C : TestClass R} {ψ : AddChar R ℂ} {JA : Matrix (Fin m) (Fin m) (R ⊗[F] E)}
  {χ : (R ⊗[F] E)ˣ →* Circle} {κ : Type} [Fintype κ] {d : LocDbx σ JA Q κ}
  {om : UG (conjR R σ) (JR R Q) →* Module.End ℂ ((κ → R) → ℂ)} {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} {K : Subgroup (HA R σ Q)}
  {f : HA R σ Q → ℂ}

end Model

end GlobalTheory.LocSW

end
