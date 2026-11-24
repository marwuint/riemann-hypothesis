module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulInvPiGMemN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.SemiT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {R : Type}
  [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  rw [piMat, PI.LevelKSplit.W.SemiG.Dat.Pi, map_add (f := _), LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', Matrix.mul_assoc]

theorem continuous_piMat : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : (fun g : HA R σ J => piMat (P := P) (T := T) g) = fun g =>
      LinearMap.toMatrix' (datR R σ J P T).pU + LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := funext piMat_eq
  rw [he]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

theorem continuous_piMat_inv : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  exact (continuous_piMat (P := P) (T := T)).comp continuous_inv


variable (R) in
def fwdM (hP : P.IsStd σ J T) (p : Nsub R σ J P × Hsub R σ J P) : Ssub R σ J P :=
  ⟨(p.1 : HA R σ J) * (p.2 : HA R σ J), (Ssub R σ J P).mul_mem (N_le_S' (R := R) hP p.1.2) (H_le_S p.2.2)⟩

theorem continuous_fwdM (hP : P.IsStd σ J T) : Continuous (fwdM R hP) := by
  apply continuous_induced_rng.2
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem continuous_piG : Continuous fun s : Ssub R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_piMat (P := P) (T := T)).comp continuous_subtype_val
  · exact (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val


variable (R) in
def bwdM (s : Ssub R σ J P) : Nsub R σ J P × Hsub R σ J P :=
  (⟨(s : HA R σ J) * (piG (R := R) hσσ hJ hP (s : HA R σ J) s.2)⁻¹, mul_inv_piG_mem_N hσσ hJ hP s.2⟩,
    ⟨piG (R := R) hσσ hJ hP (s : HA R σ J) s.2, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩)

theorem continuous_bwdM : Continuous (bwdM R hσσ hJ hP) := by
  have hpi := continuous_piG (R := R) hσσ hJ hP
  refine Continuous.prodMk ?_ ?_
  · exact continuous_induced_rng.2 (continuous_subtype_val.mul hpi.inv)
  · exact continuous_induced_rng.2 hpi

theorem bwd_fwd : Function.LeftInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  rintro ⟨n, h⟩
  have hnS := N_le_S' (R := R) hP n.2
  have hhS := H_le_S (R := R) h.2
  have key : piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J))
      ((Ssub R σ J P).mul_mem hnS hhS) = h := by
    rw [piG_mul hσσ hJ hP hnS hhS, piG_of_N hσσ hJ hP n.2 hnS, piG_of_H hσσ hJ hP h.2 hhS, one_mul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (n : HA R σ J) * (h : HA R σ J) *
      (piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) _)⁻¹ = n
    rw [key, mul_inv_cancel_right]
  · exact key

theorem fwd_bwd : Function.RightInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  exact fun s => Subtype.ext (inv_mul_cancel_right _ _)


variable (R) in
def homeoNH : (Nsub R σ J P × Hsub R σ J P) ≃ₜ Ssub R σ J P where
  toFun := fwdM R hP
  invFun := bwdM R hσσ hJ hP
  left_inv := bwd_fwd hσσ hJ hP
  right_inv := fwd_bwd hσσ hJ hP
  continuous_toFun := continuous_fwdM hP
  continuous_invFun := continuous_bwdM (R := R) hσσ hJ hP

theorem semi_gen : Semi (Ssub R σ J P) (Nsub R σ J P) (Hsub R σ J P) :=
  ⟨fun _ hh _ hn => norm_N hh hn, homeoNH R hσσ hJ hP, fun _ => rfl⟩

end Cont

theorem semidirect_topological_all : PI.LevelKSplit.W.ExS.SemiNHSAll := by
  unfold PI.LevelKSplit.W.ExS.SemiNHSAll PI.LevelKSplit.ForAllCM PI.LevelKSplit.W.ExS.SemiNHS
  intro F E _ _ _ _ _ σ _ M J _ hJ hσσ r P T hP
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact semi_gen hσσ hJ hP

end PI.LevelKSplit.W.SemiT
