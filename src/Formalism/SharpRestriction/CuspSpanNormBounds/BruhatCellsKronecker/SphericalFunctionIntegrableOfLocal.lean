import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

theorem one_mem_rational_points (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hP]
  · simp [AutInst.fmat]

structure CData : Type 1 where
  I : AutInst
  b : ℝ
  lam : InfinitePlace I.F → Fin I.n → ℝ
  g : ℕ
  g₀ : ℕ
  e : I.Gf → ℂ
  H : InfinitePlace I.F → Type
  [hN : ∀ v, NormedAddCommGroup (H v)]
  [hI : ∀ v, InnerProductSpace ℂ (H v)]
  [hC : ∀ v, CompleteSpace (H v)]
  σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)
  w : ∀ v, H v
  Hs : Type
  [sN : NormedAddCommGroup Hs]
  [sI : InnerProductSpace ℂ Hs]
  [sC : CompleteSpace Hs]
  σs : I.Ginf → (Hs →L[ℂ] Hs)
  tens : (∀ v, H v) → Hs
  μf : Measure I.Gf
  [sf : SigmaFinite μf]
  fund : Set I.GA
  R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)
  Re : I.L2 μf fund →L[ℂ] I.L2 μf fund
  h : ℝ

attribute [instance] CData.hN CData.hI CData.hC CData.sN CData.sI CData.sC CData.sf

namespace CData

variable (X : CData)

abbrev L2 : Type := X.I.L2 X.μf X.fund

def φ : X.I.GA → ℂ := phe X.I (phOf X.I X.σ X.w) X.e

def μ : Measure X.I.GA := (X.I.muA X.μf).restrict X.fund

def Dc : ℝ := (X.I.Dcount X.σs X.μf X.fund X.R X.Re : ℝ)

def Ds : ℝ := X.I.Dstar (fdegAll X.I X.σ X.w) X.μf X.fund X.e

def one' : X.I.GFset := ⟨1, one_mem_rational_points X.I⟩

end CData

namespace CData

end CData

namespace CData

end CData

def cartanDistance {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)}

namespace CData

variable (X : CData)

def dist (x : X.I.GA) (γ : X.I.GFset) (v : InfinitePlace X.I.F) : ℝ :=
  cartanDistance (X.I.ε v) ((x⁻¹ * (γ : X.I.GA) * x).1 v)

end CData

namespace CData

end CData

namespace CData

end CData

namespace CData

variable (X : CData)

def qq : ℕ := Finset.univ.sup fun v => q0At X.I v

end CData

namespace CData

end CData

end Formalism.MainNotions.BridgeLemma

end
