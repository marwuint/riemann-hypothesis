import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.L2.Indef.Examples₂

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

section Diag

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def only0 (V : Type) [AddCommGroup V] [Module K V] : Fin 2 → Submodule K V := ![⊤, ⊥]

end Diag

namespace three

variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K) (kap : ℝ)
  (l : Fin 2 → Fin 2 → ℝ)

abbrev base : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := Unit
  μ0 := ()
  Ix := Fin 2
  fIx := inferInstance
  J := Fin 2
  fJ := inferInstance

abbrev df1 : DefSide (base K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => sl K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ => fr K 1
  Qp := fun _ => only0 (Fin 1 → K)
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 1
  Tl := fun _ _ => sl K 1
  Zp := fun _ _ => only0 (Fin 1 → K)

abbrev dat1 : IndefData (df1 K v0) where
  μ := fun _ => ()
  Tw := ∅
  D := 1
  XE := scaleFrame (fun _ => kap * ∏ j, l j 0) (fr K 1)
  Ep := only0 (Fin 1 → K)
  ι := fun _ => 1
  dW := fun _ => 1
  XW := fun j => scaleFrame (fun _ => l j 0) (fr K 1)
  Wp := fun _ => only0 (Fin 1 → K)
  M := fun _ => sl K 1
  θ := fun _ _ => 1
  κ := fun _ => kap
  lam := fun j _ p _ => l j p
  err0 := fun _ _ => 0

variable {K v0 kap l}

variable (K v0) in

abbrev dc : DefCols (df1 K v0) where
  Mem := Unit
  a := fun _ => 1
  Xc := fun _ => fr K 1
  Pt := fun _ _ => (Pi.basisFun K (Fin 1)).toDual

variable (K v0) in

abbrev sp : SPer (dc K v0) where
  HH := ℂ
  nHH := inferInstance
  iHH := inferInstance
  Pu := fun _ => LinearMap.proj 0
  Rw := ⊤

end three

namespace four

open scoped Classical

variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (b : Fin 2 → Fin 2 → K) (kap : ℝ) (l : Fin 2 → Fin 2 → ℝ)

abbrev base : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := Bool
  μ0 := false
  Ix := Fin 2
  fIx := inferInstance
  J := Fin 2
  fJ := inferInstance

abbrev df1 : DefSide (base K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => sl K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ => fr K 1
  Qp := fun _ => only0 (Fin 1 → K)
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 1
  Tl := fun _ _ => sl K 1
  Zp := fun _ _ => only0 (Fin 1 → K)

def bT (t : Bool) (j p : Fin 2) : K := cond t (b j p) 1

def aT (t : Bool) (p : Fin 2) : K := ∏ j, bT K b t j p

variable {K v0 S b kap l}

variable (K v0 b) in

abbrev dc : DefCols (df1 K v0) where
  Mem := Unit
  a := fun _ => 1
  Xc := fun _ => fr K 1
  Pt := fun _ t => aT K b t 0 • (Pi.basisFun K (Fin 1)).toDual

variable (K v0 b) in

abbrev sp : SPer (dc K v0 b) where
  HH := ℂ
  nHH := inferInstance
  iHH := inferInstance
  Pu := fun _ => LinearMap.proj 0
  Rw := ⊤

end four

end Formalism.L2.Indef.Examples₂
