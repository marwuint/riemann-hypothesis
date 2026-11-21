import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB

open MvPolynomial GroundTheory.Heights₂.Heights

section Objects

variable {T : Type*} [Fintype T] [DecidableEq T] {N : ℕ}

def entry (lam : T × Fin N → ℝ) (τ : T) (i : ℕ) : ℝ :=
  if h : i < N then lam (τ, ⟨i, h⟩) else 0

def gapAtIndex (lam : T × Fin N → ℝ) (τ : T) (i : ℕ) : ℝ :=
  entry lam τ i - entry lam τ (i + 1)

def ncGap (j : ℕ) (lam : T × Fin N → ℝ) (τ : T) : ℝ :=
  gapAtIndex lam τ (j - 1)

def IsDominantWeight (lam : T × Fin N → ℝ) : Prop :=
  ∀ τ i, i + 1 < N → 0 ≤ gapAtIndex lam τ i

def IsRatVec (lam : T × Fin N → ℝ) : Prop := ∀ p, ∃ q : ℚ, lam p = q

def IsRatNum (s : ℝ) : Prop := ∃ q : ℚ, s = q

def sumNorm (lam : T × Fin N → ℝ) : ℝ := ∑ p, |lam p|

def linForm (lam : T × Fin N → ℝ) : MvPolynomial (T × Fin N) ℝ :=
  -∑ p, lam p • X p

def evalS (lam : T × Fin N → ℝ) (s : ℝ) (Q : MvPolynomial (Option (T × Fin N)) ℝ) : ℝ :=
  eval (fun o => o.elim s lam) Q

variable (T N)

def fullAct (w : T → Equiv.Perm (Fin N)) (p : T × Fin N) : T × Fin N := (p.1, w p.1 p.2)

def fullSign (w : T → Equiv.Perm (Fin N)) : ℝ := ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def basePoint : T × Fin N → ℝ := fun p => -(p.2.val : ℝ)

def flagDegree : MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ antisymDegree T N / eval (basePoint T N) (antisymDelta T N)) •
    ∑ w : T → Equiv.Perm (Fin N), fullSign T N w •
      ((aeval fun p => basePoint T N (fullAct T N w p)).toLinearMap ∘ₗ
        homogeneousComponent (antisymDegree T N))

def degFl (lam : T × Fin N → ℝ) : ℝ := flagDegree T N (linForm lam ^ antisymDegree T N)

variable {T N}

end Objects

structure VolumeSystem (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp]
    (Cl : Type) [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) where
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N
  card_mul_gt : 2 < Fintype.card T * (N - 1)
  vol : ℝ
  vol_pos : 0 < vol
  P : ℕ → MvPolynomial (T × Fin N) ℝ
  Ps : ℕ → MvPolynomial (Option (T × Fin N)) ℝ
  C2 : ℝ
  second_volume_constant_nonneg : 0 ≤ C2
  P_homogeneous : ∀ B : ℕ, 2 ≤ B → (P B).IsHomogeneous (antisymDegree T N + 1)
  Ps_totalDegree : ∀ B : ℕ, 2 ≤ B → (Ps B).totalDegree ≤ antisymDegree T N + 1
  Ps_at_zero : ∀ B : ℕ, 2 ≤ B → ∀ lam, evalS lam 0 (Ps B) = eval lam (P B)
  P_coeff : ∀ B : ℕ, 2 ≤ B → ∀ m, |coeff m (P B)| ≤ C2 * Real.log B
  Ps_coeff : ∀ B : ℕ, 2 ≤ B → ∀ m, |coeff m (Ps B)| ≤ C2 * Real.log B
  w0 : T × Fin N → ℝ
  L : (T × Fin N → ℝ) →ₗ[ℝ] Cl
  A' : Cl
  bd' : Cl
  A'_eq : A' = L w0 - bd'
  nef : Set Cl
  ample : Set Cl
  effective : Set Cl
  nef_add : ∀ a ∈ nef, ∀ b ∈ nef, a + b ∈ nef
  nef_smul : ∀ t : ℝ, 0 ≤ t → ∀ a ∈ nef, t • a ∈ nef
  ample_subset_nef : ample ⊆ nef
  L_nef : ∀ lam, IsDominantWeight lam → L lam ∈ nef
  A'_ample : A' ∈ ample
  bd'_effective : bd' ∈ effective
  inter : Comp → MultilinearMap ℝ (fun _ : Fin (antisymDegree T N) => Cl) ℝ
  inter_symm : ∀ c v (σ : Equiv.Perm (Fin (antisymDegree T N))), inter c (v ∘ σ) = inter c v
  kleiman_nef : ∀ c v, (∀ i, v i ∈ nef) → 0 ≤ inter c v
  kleiman_effective : ∀ c v i₀, v i₀ ∈ effective → (∀ i, i ≠ i₀ → v i ∈ nef) → 0 ≤ inter c v
  inter_L : ∀ lam, ∑ c, inter c (fun _ => L lam) = vol * degFl T N lam
  Mbar : ℕ → (T × Fin N → ℝ) → ℝ → Comp → ℝ
  height : ℕ → (T × Fin N → ℝ) → ℝ → Pt → ℝ
  compOf : Pt → Comp
  zdense : Comp → Set Pt → Prop
  zdense_nonempty : ∀ c S, zdense c S → ∃ y ∈ S, compOf y = c
  zdense_mono : ∀ c S S', zdense c S → S ⊆ S' → zdense c S'
  arithNef : ℕ → (T × Fin N → ℝ) → ℝ → Prop
  s0 : ℝ
  one_le_localLevel : 0 < s0
  C3 : ℝ
  C3_nonneg : 0 ≤ C3
  agreement : ∀ B : ℕ, 2 ≤ B → ∀ lam s, IsRatVec lam → IsRatNum s → ‖lam‖ ≤ 1 → 0 < s → s ≤ s0 →
    IsDominantWeight (lam - s • w0) →
    |∑ c, Mbar B lam s c - evalS (lam - s • w0) s (Ps B)| ≤ C3 * s
  nefness : ∀ B : ℕ, 2 ≤ B → ∀ lam s, IsRatVec lam → IsRatNum s →
    sumNorm lam ≤ Fintype.card T * N → 0 < s → s ≤ s0 → IsDominantWeight (lam - s • w0) →
    (∀ τ, 4 * Fintype.card T * ‖lam - s • w0‖ ≤ ((B : ℝ) - 2) * ncGap j (lam - s • w0) τ) →
    arithNef B lam s
  moriwaki_lower : ∀ B : ℕ, 2 ≤ B → ∀ lam s c (e : ℝ), arithNef B lam s →
    (∀ y, compOf y = c → e ≤ height B lam s y) →
    (antisymDegree T N + 1 : ℝ) * e * inter c (fun _ => L lam - s • bd') ≤ Mbar B lam s c
  moriwaki_upper : ∀ B : ℕ, 2 ≤ B → ∀ lam s c (e : ℝ) S, arithNef B lam s → zdense c S →
    (∀ y ∈ S, height B lam s y ≤ e) →
    Mbar B lam s c ≤ (antisymDegree T N + 1 : ℝ) * e * inter c (fun _ => L lam - s • bd')
  ta0 : ℝ → ℝ
  C4 : ℝ → ℝ
  tauZero_pos : ∀ c₀, 0 < c₀ → c₀ ≤ 1 → 0 < ta0 c₀
  initial_radius_small : ∀ c₀, 0 < c₀ → c₀ ≤ 1 → ta0 c₀ ≤ 1 / 2 ∧ 2 * (2 * ‖w0‖) * ta0 c₀ ≤ 1 ∧
    2 * (2 * ‖w0‖) * ta0 c₀ ^ 2 ≤ c₀ ∧ ta0 c₀ ^ 2 ≤ s0
  C4_nonneg : ∀ c₀, 0 ≤ C4 c₀
  height_lower : ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) →
    ∀ y, -(C4 c₀ * Real.log (B / ta ^ 2)) ≤ height B lam (ta ^ 2) y
  C5 : ℝ
  fifth_volume_constant_nonneg : 0 ≤ C5
  height_upper : ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) →
    ∀ c, ∃ S, zdense c S ∧ ∀ y ∈ S, height B lam (ta ^ 2) y ≤ C5 * Real.log B
  hFl : MvPolynomial (T × Fin N) ℝ
  antisymmetry : ∀ B : ℕ, 2 ≤ B → ∀ σ, IsBlockSimpleSwap T N j σ →
    rename σ (P B - vol • hFl) = -(P B - vol • hFl)
  hFl_homogeneous : hFl.IsHomogeneous (antisymDegree T N + 1)
  hFl_wall : ∀ lam, IsDominantWeight lam → (∃ τ, ncGap j lam τ = 0) → eval lam hFl = 0
  hFl_nonneg : ∀ lam, IsDominantWeight lam → 0 ≤ eval lam hFl

namespace VolumeSystem

end VolumeSystem

set_option linter.dupNamespace false

section Inhabitants

theorem cons_three_two {α : Type} (a : α) (v : Fin 2 → α) : (Fin.cons a v : Fin 3 → α) 2 = v 1 := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB
