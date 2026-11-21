import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

def ptTable {R : Type} [CommRing R] {ι : Type} {a b : ℕ} (ap : ι → Matrix (Fin a) (Fin b) R)
    (m : DVar ι a b →₀ ℕ) : R :=
  m.prod fun k e => ap k.1 k.2.2 k.2.1 ^ e

def substAdj {K : Type} [Field K] {ι : Type} {a b : ℕ} (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) K) :
    Pol K ι a →ₐ[K] Pol K ι b :=
  aeval fun v => ∑ β : Fin b, C (ap v.1 v.2.1 β) * X (v.1, β, Fin.castLE hab v.2.2)

def sharp {K : Type} [Field K] {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (P : Pol K ι a) : Pol K ι a :=
  P * ∏ τ, frDet K a τ ^ n τ

def WtCompat {ι : Type} {a b : ℕ} (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (s s' : ι → ℤ) (n : ι → ℕ) : Prop :=
  (∀ τ (i : Fin a), (lam' τ).w (Fin.castLE hab.le i) + s τ = (lam τ).w i + s' τ) ∧
  (∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).w j = -s τ) ∧
  ∀ τ, (n τ : ℤ) = (lam τ).detShift + s' τ

def InDeg {ι : Type} {a b : ℕ} (lam : ι → DomWeight a) (s' : ι → ℤ) (m : DVar ι a b →₀ ℕ) : Prop :=
  ∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) = ∑ i : Fin a, ((lam τ).w i + s' τ)

section Lat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

def HAt {a : ℕ} (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) :
    Submodule (𝓞 K) (VV K lam) :=
  localization₂ w.asIdeal (nabK lam fun τ => dualFr (M τ))

def detFac {a b : ℕ} (s s' : ι → ℤ) (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K) : K :=
  ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ * (BW τ : Matrix (Fin b) (Fin b) K).det ^ (-s τ)

def LatWithBasis {a : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin a → K))
    (B : ι → GL (Fin a) K) : Prop :=
  ∀ τ, (M τ).FG ∧ IsBasisAt w (M τ) (B τ)

def extLat {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a : ℕ}
    (M : Submodule (𝓞 K) (Fin a → K)) : Submodule v.integer (Fin a → L) :=
  Submodule.span v.integer ((fun (x : Fin a → K) (i : Fin a) => σ (x i)) '' (M : Set (Fin a → K)))

def admitted {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a b : ℕ}
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (ap : ι → Matrix (Fin a) (Fin b) L) : Prop :=
  ∀ τ, ∀ y ∈ extLat v σ (MW τ), ap τ *ᵥ y ∈ extLat v σ (M τ)

def InClosure {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a b : ℕ}
    (lam : ι → DomWeight a) (s' : ι → ℤ)
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (κ : K) (J : (DVar ι a b →₀ ℕ) → K) : Prop :=
  ∀ ε : K, ε ≠ 0 → ∃ (k : ℕ) (c : Fin k → L) (ap : Fin k → ι → Matrix (Fin a) (Fin b) L),
    (∀ i, v (c i) ≤ 1) ∧ (∀ i, admitted v σ M MW (ap i)) ∧
    ∀ m, InDeg lam s' m → v (σ (J m) - σ κ * ∑ i, c i * ptTable (ap i) m) ≤ v (σ ε)

end Lat

def DetIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r : ℕ) (B B' : GL (Fin r) K)
    (M' : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (q : K), q ≠ 0 →
    localization₂ w.asIdeal M' = localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun α : Fin r =>
      (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j)) →
    IsBasisAt w M' B' →
    w.valuation K (B' : Matrix (Fin r) (Fin r) K).det = w.valuation K (q * (B : Matrix (Fin r) (Fin r) K).det)

def PointIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
      (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K), LatWithBasis w M B → LatWithBasis w MW BW →
    ∀ ap : ι → Matrix (Fin a) (Fin b) K, (∀ τ, ∀ y ∈ MW τ, ap τ *ᵥ y ∈ localization₂ w.asIdeal (M τ)) →
    ∀ F ∈ HAt w lam M, ∃ G ∈ HAt w lam' MW, jetOp lam lam' (ptTable ap) n F = detFac s s' B BW • G

def ClosureIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L),
    (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
      (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
      (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K), LatWithBasis w M B → LatWithBasis w MW BW →
    ∀ (κ : K) (J : (DVar ι a b →₀ ℕ) → K), InClosure v σ lam s' M MW κ J →
    ∀ F ∈ HAt w lam M, ∃ G ∈ HAt w lam' MW, jetOp lam lam' J n F = (κ * detFac s s' B BW) • G

end GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
