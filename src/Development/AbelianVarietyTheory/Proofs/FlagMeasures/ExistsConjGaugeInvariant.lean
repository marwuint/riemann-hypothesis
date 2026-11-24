module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MuGPreimageConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

def innerAutTop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (s : G) : G ≃ₜ* G :=
  { MulAut.conj s with
    continuous_toFun := by
      change Continuous fun g : G => s * g * s⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun g : G => s⁻¹ * g * s
      fun_prop }

theorem inUJ_map_conj {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (g.map (starRingEnd ℂ)) := by
  unfold Formalism.REAL.inUJ at hg ⊢
  have hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h2
  rwa [hH]

noncomputable def conjUJHom {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε →* Formalism.REAL.UJ ε :=
  ((Units.map ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom).comp (Formalism.REAL.UJ ε).subtype).codRestrict
    (Formalism.REAL.UJ ε) fun g => inUJ_map_conj ε g.2

theorem uMat_conjUJHom {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    uMat (conjUJHom ε g) = (uMat g).map (starRingEnd ℂ) := rfl

theorem conjUJHom_invol {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : conjUJHom ε (conjUJHom ε g) = g := by
  apply Subtype.ext
  apply Units.ext
  show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g
  rw [uMat_conjUJHom, uMat_conjUJHom]
  ext i j
  simp

theorem continuous_conjUJHom {n : ℕ} (ε : Fin n → Bool) : Continuous (conjUJHom ε) := by
  have hc : Continuous ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom := by
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  exact Continuous.subtype_mk ((Continuous.units_map _ hc).comp continuous_subtype_val) _

noncomputable def conjUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε where
  toFun := conjUJHom ε
  invFun := conjUJHom ε
  left_inv := conjUJHom_invol ε
  right_inv := conjUJHom_invol ε
  map_mul' := map_mul _
  continuous_toFun := continuous_conjUJHom ε
  continuous_invFun := continuous_conjUJHom ε

theorem gauge_map_inner_comp {n : ℕ} (ε : Fin n → Bool) (C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε)
    (hC : ∀ g, Formalism.REAL.hs (uMat (C g) - 1) = Formalism.REAL.hs (uMat g - 1)) (s : Formalism.REAL.UJ ε) (c : ℝ)
    (hc : IsGauge ε c) :
    (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g := by
    intro g
    show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g
    simp only [map_mul, map_inv, C.apply_symm_apply]
    group
  have key := gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹)
    (fun g => by rw [hT]; exact hC g) c c hc hc
  have hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s)) := by
    funext g
    rfl
  rwa [hf]

theorem exists_conj_gauge_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (τ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → ∃ C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (C g) = (uMat g).map τ) ∧ ∀ (s : Formalism.REAL.UJ ε) (c : ℝ), IsGauge ε c → (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  intro n ε τ hτ
  rcases hτ with rfl | rfl
  · refine ⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩
    · ext i j
      simp
    · exact gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc
  · refine ⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩
    refine gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc
    have h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ) := uMat_conjUJHom ε g
    rw [h1]
    unfold Formalism.REAL.hs
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_conj]

end GlobalTheory.LeviIso
