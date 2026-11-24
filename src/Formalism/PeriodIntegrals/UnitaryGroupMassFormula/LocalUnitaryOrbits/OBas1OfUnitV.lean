module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfUnitV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NearTIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OBas1 : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∃ e : Fin n → Fin n → Fv F v ⊗[F] E, Orb.IsOBas v Λ e ∧ gramR (Fv F v) σ J e = 1

def ResAlg : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (π : OR (E := E) v →+* K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          IsRes σ v ϖ (σ' : K →+* K) π) ∨
       (etaV (E := E) v = 1 ∧ ∃ π : OR (E := E) v →+* k × k,
          IsRes σ v ϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π))

theorem oBas1_of_unitV (hU : Orb.UnitV σ J ψ v Λ) : OBas1 σ J ψ v Λ := by
  intro hstd hL hsd hun
  obtain ⟨e, he, -, he1, hsp⟩ := Orb.orthoGen σ J ψ v Λ hU hstd hL hsd hun n (Fin 0)
    (fun i => i.elim0) (by simp) (fun i => i.elim0) ⟨1, (Orb.oSub v).1, by simp [Matrix.det_isEmpty]⟩
  refine ⟨e, fun x => ⟨fun hx => hsp x ⟨hx, fun i => i.elim0⟩, ?_⟩, he1⟩
  rintro ⟨c, hc, rfl⟩
  exact Submodule.sum_mem _ fun i _ => Orb.oSmul v Λ hL (c i) (hc i) (e i) (he i).1

theorem det_red {K : Type} [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ}
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v)
    {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) (hd : T.det * w = 1) :
    IsUnit (Matrix.det (fun i j => π ⟨T i j, hT i j⟩)) := by
  set Ts : Matrix (Fin a) (Fin a) (OR (E := E) v) := fun i j => ⟨T i j, hT i j⟩
  have hdet : ((Ts.det : OR (E := E) v) : Fv F v ⊗[F] E) = T.det := by
    rw [show ((Ts.det : OR (E := E) v) : Fv F v ⊗[F] E) = (OR (E := E) v).subtype Ts.det from rfl,
      RingHom.map_det]
    rfl
  have hm : Ts.det * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    rwa [Subring.coe_mul, hdet]
  have hu : IsUnit Ts.det := ⟨⟨Ts.det, ⟨w, hw⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  have := hu.map π
  rwa [RingHom.map_det] at this

theorem redU_of (hU : Orb.UnitV σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ) (Y : TupV (E := E) v n a) :
    RedU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hG.2.1 hG.2.2.1 hG.2.2.2.1
  have hT := gY_mem σ J ψ v Λ hG
  obtain ⟨w, hw, -, hd⟩ := hG.2.2.2.2.2.2
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, det_red v π _ hT hw hd,
      card_cls σ J v Λ hcm hJ hG.2.2.1 he he1 (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · exact fun i j => (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, det_red v π _ hT hw hd,
      card_cls σ J v Λ hcm hJ hG.2.2.1 he he1 (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · exact fun i j => (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmLocU.Red
