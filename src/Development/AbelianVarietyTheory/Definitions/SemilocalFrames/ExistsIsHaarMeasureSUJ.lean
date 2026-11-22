import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLocGrowthA

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DSSU

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def SUset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | g ∈ UJset ε ∧ g.det = 1}

def KS (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | g ∈ Kset ε ∧ g.det = 1}

def SUJ (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | (umat g).det = 1}
  one_mem' := by simp [umat]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, umat, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul] at *
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, umat] at *
    have h : ((a⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1 := by
      rw [← Units.val_mul]; simp
    have h2 := congrArg Matrix.det h
    rwa [Matrix.det_mul, ha, mul_one, Matrix.det_one] at h2

def rhoCh (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => lam b < lam a ∧ ε b = ε a).card : ℝ) -
    ((univ.filter fun b => lam a < lam b ∧ ε b = ε a).card : ℝ)) / 2

def rhoNh (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card : ℝ) -
    ((univ.filter fun b => lam a < lam b ∧ ε b ≠ ε a).card : ℝ)) / 2

def lowCh (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoNh ε lam - rhoCh ε lam

def Above (P : Fin n → Fin n → Prop) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → P a b) ∧ Λ = μ + ∑ a, ∑ b, (c a b : ℝ) • root a b

def IsParS (lam : Fin n → ℝ) : Prop :=
  ∑ a, lam a = 0 ∧ Function.Injective lam ∧ ∀ a b, ∃ m : ℤ, lam a - lam b = (m : ℝ)

def E0 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single a b 1 - (if a = b then (n : ℂ)⁻¹ else 0) • (1 : Matrix (Fin n) (Fin n) ℂ)

def EwordS (ε : Fin n → Bool) (w : List (Fin n × Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  w.foldr (fun p G => Ec ε (E0 p.1 p.2) G) f

def gelfS (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (m + 1) → Fin n, EwordS ε (cycWord a) f g

def SmoothS (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀ ∈ SUset ε, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ SUset ε → f g = F g

section Rep

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def IsSqIntS (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ μ : Measure (SUJ ε), μ.IsHaarMeasure → ∀ v w : H, MemLp (fun g : SUJ ε => ⟪w, σ (umat g.1) v⟫_ℂ) 2 μ

def IsSqIntIrrS (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (SUset ε) σ ∧ IsIrredOn (SUset ε) σ ∧ IsSqIntS ε σ

def Stable (K : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S

def IsKFinS (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ Stable (KS ε) σ S

def HasInfCharS (ε : Fin n → Bool) (χ : Fin n → ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, IsKFinS ε σ v → IsKFinS ε σ w →
    SmoothS ε (fun g => ⟪w, σ g v⟫_ℂ) ∧
      ∀ m : ℕ, ∀ g ∈ SUset ε, gelfS ε m (fun g => ⟪w, σ g v⟫_ℂ) g = gelfVal χ (m + 1) * ⟪w, σ g v⟫_ℂ

def IsWtS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, ∑ a, θ a = 0 →
    σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v

def IsKTypeS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  ∑ a, Λ a = 0 ∧ FiniteDimensional ℂ S ∧ Stable (KS ε) σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → Stable (KS ε) σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtS σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), ∑ a, μ a = 0 → v ∈ S → v ≠ 0 → IsWtS σ μ v →
      Above (fun a b => lam b < lam a ∧ ε a = ε b) μ Λ

def IsHCS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsSqIntIrrS ε σ ∧ HasInfCharS ε (fun a => (lam a : ℂ)) σ ∧
    (∃! S : Submodule ℂ H, IsKTypeS ε lam σ (lowCh ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeS ε lam σ μ S → Above (fun a b => lam b < lam a) (lowCh ε lam) μ

def EquivOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  ∃ T : H ≃ₗᵢ[ℂ] H', ∀ g ∈ G, ∀ v, T (σ g v) = σ' g (T v)

def Ext (ε : Fin n → Bool) (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, π (z • g) = z ^ m • π' g

end Rep

structure Fam (n : ℕ) : Type 1 where
  H : (Fin n → ℝ) → Type
  nacg : ∀ lam, NormedAddCommGroup (H lam)
  ips : ∀ lam, InnerProductSpace ℂ (H lam)
  π : ∀ lam, Matrix (Fin n) (Fin n) ℂ → (H lam →L[ℂ] H lam)

attribute [instance] Fam.nacg Fam.ips

def ConjK (ε : Fin n → Bool) (lam lam' : Fin n → ℝ) : Prop :=
  ∃ w : Equiv.Perm (Fin n), (∀ a, ε (w a) = ε a) ∧ lam' = lam ∘ w

def ParamS (ε : Fin n → Bool) (F : Fam n) : Prop :=
  (∀ lam, IsParS lam → IsHCS ε lam (F.π lam)) ∧
    ∀ lam lam', IsParS lam → IsParS lam' → (EquivOn (SUset ε) (F.π lam) (F.π lam') ↔ ConjK ε lam lam')

def ExhaustS (ε : Fin n → Bool) (F : Fam n) : Prop :=
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsSqIntIrrS ε σ → ∃ lam, IsParS lam ∧ EquivOn (SUset ε) σ (F.π lam)

def ClassS (ε : Fin n → Bool) : Prop := ∃ F : Fam n, ParamS ε F ∧ ExhaustS ε F

end GlobalTheory.DSSU

end
