import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem coef_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : VecNe R i t) (μ) (𝓕)
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) : coef R i t μ 𝓕 1 = 1 := by
  unfold coef
  have : R.ωP i t (1, 1) = 1 := map_one _
  rw [this]
  exact div_self (h μ 𝓕 hμ).1

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem coef_mul_lev (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : LevFix R i t) (μ) (𝓕) (g k : GA D (Wc D i))
    (hk : k ∈ levW R i) : coef R i t μ 𝓕 (g * k) = coef R i t μ 𝓕 g := by
  unfold coef
  have e : R.ωP i t (1, g * k) = R.ωP i t (1, g) * R.ωP i t (1, k) := by rw [← map_mul]; simp
  have hv := h k hk 1
  rw [pureTensor_one] at hv
  rw [e, Module.End.mul_apply, hv]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 ∧ SuppF V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  constructor <;> intro a b <;> simp [this]

end GlobalTheory.RawLift.Model

end
