import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValApplySubLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

def RatioConj : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ →
    ∀ (Ω : Type) [Field Ω] [Algebra H.K Ω] [IsAlgClosure H.K Ω] (j : Ω →+* ℂ) (τ₀ : I),
    (∀ x : H.K, j (algebraMap H.K Ω x) = φ τ₀ x) →
    ∀ art : Ideles H.K →* Gab H.K Ω, IsGlobalArtin art →
    ∀ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ → T₀ ≠ 0 →
    ∀ Q : Finset (HeightOneSpectrum (OF H.E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → Finite (PicO (condQ 𝔣 Q)) →
    ∀ T : PicO (condQ 𝔣 Q) → ℂ, (∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q)) →
    ∃ ρ : (PicO (condQ 𝔣 Q) →* Ωˣ) → Ω,
      (∀ ψ, j (ρ ψ) = (∑ᶠ q, (j (ψ q))⁻¹ * T q) / T₀) ∧
      ∀ g : G H.K Ω, (∀ (x : Ω) (τ : I) (y : H.E), j x = φ τ y → g x = x) → (∀ (x : Ω) (y : (Af H.E)ˣ), j x = lamF s χ y → g x = x) →
        ∀ t : (Af H.K)ˣ, art (finIdele H.K t) = toAb H.K Ω g⁻¹ → ∀ ψ : PicO (condQ 𝔣 Q) →* Ωˣ,
          g (ρ ψ) = (g (ψ (QuotientGroup.mk (upIdele H.K H.E t))))⁻¹ * ρ ((Units.map g.toRingEquiv.toMonoidHom).comp ψ)

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def setTh (th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := th }

variable {X}

theorem toBar_algebraMap (i : X.Tw) (a : X.O0 i) :
    toBar X i (algebraMap (X.O0 i) _ a) = algebraMap (X.O i) (Kbar X i) (algebraMap (X.O0 i) (X.O i) a) := by
  rw [toBar, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  rfl

end GlobalTheory.ToricRational
