import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.HeightShare

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.BasicNotions

section Lat

variable {F : Type} [Field F] [NumberField F] [StarRing F]

def coordC (A : HLat F) (v : InfinitePlace F) (x : A.V) : A.ι → ℂ :=
  fun i => v.embedding (A.b.repr x i)

def nsq (A : HLat F) (v : InfinitePlace F) (c : A.ι → ℂ) : ℝ :=
  ∑ k, ‖(Matrix.mulVec (A.X v)⁻¹ c) k‖ ^ 2

def nrm (A : HLat F) (v : InfinitePlace F) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

theorem nrm_eq (A : HLat F) (v : InfinitePlace F) (x : A.V) :
    nrm A v x = Real.sqrt (nsq A v (coordC A v x)) := rfl

end Lat

section Data

variable {F : Type} [Field F] [NumberField F] [StarRing F]

structure LData (G : Formalism.BasicNotions.DV.Geo F) where
  Y : G.Var
  bd : G.Cl Y
  L : G.Dv Y
  W : HLat F
  ιW : W.V →ₗ[F] G.Fn Y
  n : ℕ
  w : Fin n → W.V
  abelian₂ : ℝ

namespace LData

end LData

structure HSData (G : Formalism.BasicNotions.DV.Geo F) extends LData G where
  L2 : G.Dv Y
  A : G.Dv Y
  W2 : HLat F
  ι2 : W2.V →ₗ[F] G.Fn Y
  T : ℕ
  M : ℕ → HLat F
  ιM : ∀ j, (M j).V →ₗ[F] G.Fn Y
  j0 : ℕ
  beta : ℝ
  LamD : ℝ
  LamT : ℝ
  J : ℝ

namespace HSData

end HSData

structure VData {G : Formalism.BasicNotions.DV.Geo F} (B : LData G) where
  TT : Set ℕ
  Mp : ℕ → HLat F
  io : ∀ τ, (Mp τ).V →ₗ[F] G.Fn B.Y
  delP : ℝ
  sl : ℝ
  cFin : ℕ → ℝ
  cInf : InfinitePlace F → ℝ

namespace VData

end VData

end Data

end Formalism.MainNotions.HeightShare

end
