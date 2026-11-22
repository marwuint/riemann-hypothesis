import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth
import Formalism.LocalToGlobal.IndefiniteReal.IsotInLeOfIntw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowModCanon

open MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace

theorem ipM_smul_measure {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (hne : SmNonzero M) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) {a : ℝ} (ha : 0 ≤ a) (T T' : MMap M)
    (h : ∃ c, IsMultIP M ν 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • ν) 𝓕 T T' = (a : ℂ) * ipM M ν 𝓕 T T' := by
  have h1 := ipM_spec M ν 𝓕 T T' h
  have h2 : IsMultIP M (ENNReal.ofReal a • ν) 𝓕 T T' ((a : ℂ) * ipM M ν 𝓕 T T') := by
    intro v v'
    obtain ⟨hi, he⟩ := h1 v v'
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn, Measure.restrict_smul]
      exact hi.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  have h3 := ipM_spec M _ 𝓕 T T' ⟨_, h2⟩
  choose w hw using hne
  have hw' : ∀ τ, (w τ : M.H τ) ≠ 0 := fun τ h => hw τ (Submodule.coe_eq_zero.1 h)
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hw' τ)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 h3 h2

end GlobalTheory.RowModCanon

namespace GlobalTheory.RowModCanon

end GlobalTheory.RowModCanon
