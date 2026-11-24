module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
open IsLocalRing

namespace GlobalTheory.PlaceInt

section
variable {V : Type} [CommRing V] [IsLocalRing V]

theorem mem_maximalIdeal_mvPowerSeries_iff {τ : Type} (f : MvPowerSeries τ V) :
    f ∈ maximalIdeal (MvPowerSeries τ V) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal V := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

variable [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]

theorem isAdicComplete_mvPowerSeries_finite (τ : Type) [Finite τ] :
    IsAdicComplete (maximalIdeal (MvPowerSeries τ V)) (MvPowerSeries τ V) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin τ
  have hs : ∀ {α β : Type} [Finite β] (u : β ≃ α),
      MvPowerSeries.HasSubst (fun i : β => (MvPowerSeries.X (u i) : MvPowerSeries α V)) :=
    fun _ => MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have comp : ∀ {α β : Type} [Finite α] [Finite β] (u : β ≃ α) (f : MvPowerSeries β V),
      MvPowerSeries.substAlgHom (R := V) (hs u.symm)
        (MvPowerSeries.substAlgHom (R := V) (hs u) f) = f := by
    intro α β _ _ u f
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun i : β => MvPowerSeries.substAlgHom (R := V) (hs u.symm)
        (MvPowerSeries.X (u i) : MvPowerSeries α V)) = MvPowerSeries.X := by
      funext i
      rw [MvPowerSeries.substAlgHom_X, Equiv.symm_apply_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  let E : MvPowerSeries (Fin n) V ≃+* MvPowerSeries τ V :=
    { toFun := MvPowerSeries.substAlgHom (R := V) (hs e.symm)
      invFun := MvPowerSeries.substAlgHom (R := V) (hs e)
      left_inv := comp e.symm
      right_inv := comp e
      map_mul' := map_mul _
      map_add' := map_add _ }
  have := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries V n
  exact GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv E

variable {σ τ : Type} [Finite σ] [Finite τ]

theorem exists_algHom_evC (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  refine (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, ?_⟩)).1 inferInstance V
  rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]
  exact ha j

private theorem mvPowerSeries_algHom_ext_of_X_eq (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ ψ' : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (h : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (h' : ∀ j, ψ' (MvPowerSeries.X j) = a j) : ψ = ψ' := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, by rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]; exact ha j⟩)).2
    inferInstance V ψ.toRingHom ψ'.toRingHom
    (fun t => by
      show ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)
      have hC : (MvPowerSeries.C t : MvPowerSeries σ V) = algebraMap V (MvPowerSeries σ V) t := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hC, ψ.commutes, ψ'.commutes]) h h'
  exact AlgHom.ext fun f => RingHom.congr_fun key f

theorem evC_eq_algHom (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (hψ : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (f : MvPowerSeries σ V) : evC a f = ψ f := by
  have h : ∃ φ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, φ (MvPowerSeries.X j) = a j :=
    ⟨ψ, hψ⟩
  rw [evC, dite_eq_left h, mvPowerSeries_algHom_ext_of_X_eq a ha h.choose ψ h.choose_spec hψ]

theorem constantCoeff_evC_mem (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) (f : MvPowerSeries σ V)
    (hf : MvPowerSeries.constantCoeff f ∈ maximalIdeal V) :
    MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
  rw [evC_eq_algHom a ha ψ hψ f]

  let χ₁ : MvPowerSeries σ V →+* ResidueField V :=
    (residue V).comp (MvPowerSeries.constantCoeff.comp ψ.toRingHom)
  let χ₂ : MvPowerSeries σ V →+* ResidueField V := (residue V).comp MvPowerSeries.constantCoeff
  have hC : ∀ t : V, ψ (MvPowerSeries.C t) = MvPowerSeries.C t := fun t => by
    have := ψ.commutes t
    rwa [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (ResidueField V) ⊥ σ (fun _ => 0)
    (fun _ => ⟨1, by simp⟩)).2 inferInstance V χ₁ χ₂
    (fun t => by simp [χ₁, χ₂, hC])
    (fun j => by
      simp only [χ₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψ]
      exact (residue_eq_zero_iff _).2 (ha j))
    (fun j => by simp [χ₂])
  have hf' := RingHom.congr_fun key f
  simp only [χ₁, χ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf'
  rw [← residue_eq_zero_iff, hf']
  exact (residue_eq_zero_iff _).2 hf

end

theorem evC_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  intro V _ _ _ _ _ σ τ ρ _ _ _ a ha
  refine ⟨?_, fun f hf => constantCoeff_evC_mem a ha f hf, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
    exact ⟨ψ, hψ, fun f => evC_eq_algHom a ha ψ hψ f⟩
  · intro h0 f
    have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [evC_eq_algHom a ha (MvPowerSeries.substAlgHom (R := V) hs)
      (fun j => MvPowerSeries.substAlgHom_X hs j) f]
    exact MvPowerSeries.substAlgHom_apply hs f
  · intro b hb f
    obtain ⟨ψa, hψa⟩ := exists_algHom_evC a ha
    obtain ⟨ψb, hψb⟩ := exists_algHom_evC b hb
    have hc : ∀ j, MvPowerSeries.constantCoeff (evC b (a j)) ∈ maximalIdeal V :=
      fun j => constantCoeff_evC_mem b hb (a j) (ha j)

    rw [evC_eq_algHom (fun j => evC b (a j)) hc (ψb.comp ψa)
      (fun j => by rw [AlgHom.comp_apply, hψa, evC_eq_algHom b hb ψb hψb]) f,
      evC_eq_algHom a ha ψa hψa, evC_eq_algHom b hb ψb hψb, AlgHom.comp_apply]

end GlobalTheory.PlaceInt
