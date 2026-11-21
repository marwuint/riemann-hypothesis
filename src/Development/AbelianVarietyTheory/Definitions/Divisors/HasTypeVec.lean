import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)

noncomputable section

namespace GlobalTheory.TrMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def finFn (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : GfC V → ℂ :=
  fun g => ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v (g : GA D V))

def IsFinMeas (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ν : Measure (GfC V)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∫ g, finFn V ff g ∂ν = ∏ᶠ v, ∫ x, ff v x ∂μf v

def HasTypeVec {V : HSp D} (T : TypeDataG V) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ x : W, x ≠ 0 ∧ (∀ v ∉ T.S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x) ∧
    ∀ v : T.S, x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ}

def SphRest {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  ∀ v ∉ T.S, v ≠ U.u → ∀ k ∈ Kv V v, ∀ k' ∈ Kv V v, ∀ g, ff v (k * g * k') = ff v g

def IsIrrFam {V : HSp D} {n : ℕ} {W : Fin n → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GfC V) (W i)) : Prop :=
  (∀ i, (σ i).IsIrreducible) ∧ (∀ i, IsAdmissible (σ i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))

def SpecFin : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
      mCuspDS μ σ M < Cardinal.aleph0) ∧
    ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) →
      ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
        (σs : ∀ i, Representation ℂ (GfC V) (Ws i)), IsIrrFam σs ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
          mCuspDS μ σ M ≠ 0 → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i))

def Separation : Prop :=
  ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S →
    ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs → ∀ a : Fin n → ℂ,
      (∀ ff, IsTestFin T U μf ff → SphRest T U ff →
        ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0) →
      ∀ i, HasTypeVec T (σs i) → a i = 0

end GlobalTheory.TrMult

end
