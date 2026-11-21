import Mathlib
import Formalism.QuotientMetricDivisors.DualMu
import Formalism.QuotientMetricDivisors.StatementK

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K]

def scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v

end Defs

def KappaInvariance : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ t : InfinitePlace K → ℝ, (∀ v, 0 < t v) →

      (∀ v, IsUnit (scaleFrame t XE v).det ∧
        ((scaleFrame t XE v)⁻¹).conjTranspose * (scaleFrame t XE v)⁻¹ =
          (t v : ℂ) • (((XE v)⁻¹).conjTranspose * (XE v)⁻¹)) ∧

      (∀ (d : ℕ) (XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (φ : Matrix (Fin D) (Fin d) K)
        (v : InfinitePlace K),
        detRatio XS (scaleFrame t XE) φ v = t v ^ d * detRatio XS XE φ v) ∧
      (∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
        meanLog (fun v => t v * κ v) = meanLog t + meanLog κ) ∧

      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
        lcv (scaleFrame t XE) R = lcv XE R + (D : ℝ) * meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                  (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
            meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)) XE R - meanLog t ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R - meanLog t) ∧

      (∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
        ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                  (Formalism.HN.dualFrame (scaleFrame t XE)) φ =
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame XE) φ - meanLog t)

def KappaNormalise : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
      (∀ v, IsUnit (scaleFrame (fun v => (κ v)⁻¹) XE v).det) ∧

      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (ρ P : ℝ), detRatio XS XE φ v = (κ v * ρ) ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 * ρ) ^ D * P) ∧
      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (P : ℝ), detRatio XS XE φ v = κ v ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 : ℝ) ^ D * P) ∧
      meanLog (fun _ : InfinitePlace K => (1 : ℝ)) = 0 ∧
      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) + meanLog κ ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R - meanLog κ ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                  Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
            Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R ∧
        ∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
          ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ - meanLog κ ∧
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                    Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
              Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ)

end Formalism.DivisionValues
