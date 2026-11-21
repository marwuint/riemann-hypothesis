import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnce
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevForms

theorem typeSpF_finiteDimensional : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
    FiniteDimensional K ↥(NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ hJ
  classical
  obtain ⟨N, hN, hNJ⟩ := hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  obtain ⟨Jc, hJc⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let Φ : ↥(NX.TypeSpF L n K ρ J χ) →ₗ[K] (↥(T ×ˢ Jc) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJc u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  obtain ⟨hκJ, hκ1⟩ := hNJ κ hκ
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 ⟨κ, hκJ⟩, hκ1, f.2.1 γ, h0, map_zero, Units.val_one, one_smul]

end GlobalTheory.LevForms
