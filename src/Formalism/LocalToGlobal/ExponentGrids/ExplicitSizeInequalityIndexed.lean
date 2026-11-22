import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
import Formalism.TowerValuationBounds.TowerValuationBoundIndexed

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)

noncomputable section

namespace Formalism.AtG

def gridBudgetIdx {Sq : Type} (m N : ℕ) (B BN0 Bδ : ℝ) (S0 : Finset Sq) (ee qq : Sq → ℕ) : ℝ :=
  (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 10 * N * BN0 + 2 * N + 6 * Bδ +
    4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))

def GridHeightBoundIndexed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
      (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ) (W0 : Finset (Pl K)),
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime) →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∀ l ∈ S, 0 ≤ N0 ij s l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →

    (∀ w ∈ W0, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w) +
      dd ij * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →

    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →

    0 ≤ BN0 →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∑ l ∈ S, N0 ij s l * Real.log l ≤ BN0) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →
    ∑ w ∈ W0, lw w * (vw w (∏ ij, rr w ij) : ℝ) ≤ gridBudgetIdx m N B BN0 Bδ S0 ee qq

def PassageSizeIndexed : Prop :=
  ∀ (K W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (D : ℕ), 0 < D →
    ∀ (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (kap : InfinitePlace K → ℝ)
      (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (XE v).det) → (∀ v, 0 < kap v) → (∀ v, IsUnit (X' v).det) →
    ∀ (R : Submodule (𝓞 K) (Fin D → K)) (M : Submodule (𝓞 K) W) (Ψ : (Fin D → K) →ₗ[K] W)
      (T : Finset (Pl K)) (a : Pl K → ℤ) (dF : Pl K → ℝ) (EM hInf BF p2 bb : ℝ),

    Submodule.IsLattice K R → M.FG → M ≠ ⊥ → Function.Injective Ψ →
    R.map (Ψ.restrictScalars (𝓞 K)) ≤ Formalism.HermitianLatticesTheory.idealSmul (denIdeal T a : Submodule (𝓞 K) K) M →
    muMaxDef b' X' M ≤ EM →
    htMap (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' Ψ ≤ hInf →
    ∑ w ∈ T, lw w * dF w ≤ BF →

    ∀ (Sq : Type) (m N : ℕ) (dl : Pl K → ℝ) (S Se : Finset ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
      (rr : Pl K → Fin m × Fin m → K) (zA zA' : Fin m × Fin m → K)
      (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
      (gT : Fin m × Fin m → ℤ → Pl K → ℤ) (ch : Pl K → Bool) (dd hh yy : Fin m × Fin m → ℕ)
      (S0 : Finset Sq) (cc ee qq : Sq → ℕ) (B BN0 Bδ : ℝ),
    (∀ w ∈ T, (a w : ℝ) ≤ (vw w (∏ ij, rr w ij) : ℝ) + dF w) →
    (∀ w, 0 ≤ dl w) → (∀ l ∈ S, l.Prime) →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∀ l ∈ S, 0 ≤ N0 ij s l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ij, rr w ij ≠ 0) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ T, ∀ ij, (vw w (rr w ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w) +
      dd ij * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) →
    (∀ ij, HtLe (fun _ => 0) (zA ij) B ∧ HtLe (fun _ => 0) (zA' ij) B) →
    (∀ ij s, HtLe (gT ij s) (zT ij s) B) → (∀ ij b s, HtLe (gT ij s) (zTd ij b s) B) →
    0 ≤ BN0 →
    (∀ ij, ∀ s : ℤ, 1 ≤ s → s ≤ hh ij → ∑ l ∈ S, N0 ij s l * Real.log l ≤ BN0) →
    (∀ F : Finset (Pl K), ∑ w ∈ F, lw w * dl w ≤ Bδ) →

    EM + hInf + 2 * (gridBudgetIdx m N B BN0 Bδ S0 ee qq + BF) ≤ p2 * bb →
    muMaxDef (Pi.basisFun K (Fin D)) XE R ≤ -meanLog kap + p2 * bb

end Formalism.AtG
