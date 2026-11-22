import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.InfiniteGroup
import Formalism.LocalToGlobal.Columns.DecoFin

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)

instance mulActPP {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ) : MulAction (GL (Fin n) Lc.K) (LocF.PP Lc n) where
  smul := LevModel.actPP
  one_smul p := LevModel.isAct_unique (LevModel.isAct_actPP 1 p) (fun x => by simp)
  mul_smul g h p := LevModel.isAct_unique (LevModel.isAct_actPP (g * h) p) (fun x => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 := LevModel.isAct_actPP g (LevModel.actPP h p) (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x)
    have h2 := LevModel.isAct_actPP h p x
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

def IntGL {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (O : Subring K) (g : GL ι K) : Prop :=
  ∀ a b, (g : Matrix ι ι K) a b ∈ O ∧ ((g⁻¹ : GL ι K) : Matrix ι ι K) a b ∈ O

def valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) : Subring K :=
  (Q.valuation K).valuationSubring.toSubring

theorem mem_valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ valO Q ↔ Q.valuation K x ≤ 1 :=
  Iff.rfl

def unitGL (K : Type) [Field K] [StarRing K] (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K)ᴴ * (g : Matrix (Fin n) (Fin n) K) = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) K), hg,
      Matrix.one_mul, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)ᴴ := by
      rw [← Matrix.one_mul ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← hg, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [h1, Matrix.conjTranspose_conjTranspose, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]

def latB {K ι : Type} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (B : HeightOneSpectrum (𝓞 K) → GL ι K) : Submodule (𝓞 K) (ι → K) where
  carrier := {x | ∀ Q a, ((((B Q)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) a ∈ valO Q}
  add_mem' {x y} hx hy Q a := by
    rw [Matrix.mulVec_add]; exact (valO Q).add_mem (hx Q a) (hy Q a)
  zero_mem' Q a := by rw [Matrix.mulVec_zero]; exact (valO Q).zero_mem
  smul_mem' r x hx Q a := by
    rw [← algebraMap_smul K r x, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact (valO Q).mul_mem (Q.valuation_le_one r) (hx Q a)

def spanO {K ι : Type} [Field K] [Fintype ι] (σ : K →+* ℂ) (O : Subring K) {n : ℕ} (lam : ι → DomWeight n) :
    AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ O ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = σ r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def movC {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (c : ℤ) (g : ι → GL (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  blk fun τ => roundAct ℂ n (wSh (lam τ) c) (g τ)

structure Rp {K ι : Type} [Field K] [Fintype ι] (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) (c : ℤ) where
  d : ℕ
  d_pos : 0 < d
  co : (Fin d → ℂ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ
  co_inj : Function.Injective co
  co_range : LinearMap.range co = CSpan lam
  co_int : ∀ (O : Subring K) y, co y ∈ spanO σ O lam ↔ ∀ a, ∃ r ∈ O, y a = σ r
  rho : (ι → GL (Fin n) K) →* GL (Fin d) K
  rho_co : ∀ g y, co ((rho g : Matrix (Fin d) (Fin d) K).map σ *ᵥ y) =
    movC lam c (fun τ => Matrix.GeneralLinearGroup.map σ (g τ)) (co y)
  rho_int : ∀ (O : Subring K) g, (∀ τ, IntGL O (g τ)) → IntGL O (rho g)
  H : (Fin d → ℂ) →ₗ⋆[ℂ] (Fin d → ℂ) →ₗ[ℂ] ℂ
  H_pos : ∀ y, y ≠ 0 → 0 < (H y y).re
  H_symm : ∀ y y', H y y' = starRingEnd ℂ (H y' y)
  H_rho : ∀ g : ι → GL (Fin n) K,
    (∀ τ, ((g τ : Matrix (Fin n) (Fin n) K).map σ)ᴴ * (g τ : Matrix (Fin n) (Fin n) K).map σ = 1) →
    ∀ y y', H ((rho g : Matrix (Fin d) (Fin d) K).map σ *ᵥ y) ((rho g : Matrix (Fin d) (Fin d) K).map σ *ᵥ y') = H y y'

structure Ar (D : D7) (T : ℕ) [Fact T.Prime] where
  Lc : LocF T (ZMod T)
  [st : StarRing Lc.K]
  j : Lc.K →+* D.what₂.LL
  j_star : ∀ x, D.what₂.embLL (j (star x)) = starRingEnd ℂ (D.what₂.embLL (j x))
  seen : D.what₂.places.Pl → Bool
  int_on : ∀ w, D.what₂.places.resChar w = T → ∀ x, j (if seen w then x else star x) ∈ Ow D w ↔ x ∈ Lc.O
  Γ : ∀ n, Subgroup (GL (Fin n) Lc.K)
  unit : ∀ n, Γ n ≤ unitGL Lc.K n
  int_off : ∀ n, ∀ g ∈ Γ n, ∀ w, D.what₂.places.resChar w ≠ T → ∀ a b, j ((g : Matrix (Fin n) (Fin n) Lc.K) a b) ∈ Ow D w
  free : ∀ n, ∀ g ∈ Γ n, ∀ p : LocF.PP Lc n, g • p = p → g = 1
  fin : ∀ n, Finite (MulAction.orbitRel.Quotient (Γ n) (LocF.PP Lc n))

attribute [instance] Ar.st

end GlobalTheory.LvT.Inh
