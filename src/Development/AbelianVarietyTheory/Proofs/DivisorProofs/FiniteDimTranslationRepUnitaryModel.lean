import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarisableOfCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaCplV.UnitaryTrick

theorem exists_isURep_of_core {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ K V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun k => φ (ρ k v))
    (c : InnerProductSpace.Core ℂ V) (hc : ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v) :
    ∃ (d : ℕ) (τ : K → (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
      (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)), GlobalTheory.Dec.IsURep τ ∧ ∀ k v, e (ρ k v) = τ k (e v) := by
  letI cd : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) := b.repr.toLinearEquiv
  let τ : K → (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :=
    fun g => LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap)
  have hτ : ∀ g x, τ g x = e (ρ g (e.symm x)) := fun _ _ => rfl
  have hn : ∀ g (y : V), ‖ρ g y‖ = ‖y‖ := by
    intro g y
    have h1 : inner ℂ (ρ g y) (ρ g y) = inner ℂ y y := hc g y y
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h1]
  refine ⟨_, τ, e, ⟨?_, fun a c => ?_, fun g x => ?_, fun x => ?_⟩, fun g v => ?_⟩
  · ext1 x; simp [hτ]
  · ext1 x; simp [hτ, map_mul]
  · rw [hτ]
    change ‖b.repr (ρ g (b.repr.symm x))‖ = ‖x‖
    rw [LinearIsometryEquiv.norm_map, hn, ← LinearIsometryEquiv.norm_map b.repr,
      LinearIsometryEquiv.apply_symm_apply]
  · simp only [hτ]
    exact GlobalTheory.UniTrick.continuous_lin ρ hρ e.toLinearMap _
  · rw [hτ, LinearEquiv.symm_apply_apply]

end GlobalTheory.ThetaCplV.UnitaryTrick

namespace GlobalTheory.ThetaCplV

end GlobalTheory.ThetaCplV
