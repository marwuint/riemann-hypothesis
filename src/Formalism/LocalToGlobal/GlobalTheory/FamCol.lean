import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.GlobalTheory.FamRec
import Formalism.SizeWindowBrackets.SlopeHypothesesRounded
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.LogVandermondeBounds.LogRatioUpperBound
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamCol

open Formalism Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.DIV

structure PlDat (K : Type) (I : Type) where
  N : NumDatum
  Cs : Arith.Cst
  Lv : Arith.Lev N
  sd : K
  code : I → Code N

structure RowArg {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I) where
  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]
  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]
  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ
  cc : Submodule (𝓞 K) Wd
  B : ∀ u, (C.M u).V →ₗ[K] Wd
  v : InfinitePlace K
  Y : ∀ u, Matrix (C.M u).ι (C.M u).ι ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ u, Matrix (κ ⊕ κ₁) (C.M u).ι ℂ
  γ : I → ℝ
  Bf : ∀ u, Matrix (κ ⊕ κ₁) (C.Mf u).ι ℂ
  h : I → ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] RowArg.indexWFirst RowArg.indexWSecond RowArg.indexWThird RowArg.indexWFourth RowArg.firstRealIndex RowArg.secondRealIndex RowArg.firstRationalIndex RowArg.secondRationalIndex

section Fam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def famC [IsTotallyComplex K] (m : ℕ) (C : ColObj K I) (P : PlDat K I) (R : RowArg C) : LChain2.Fam I m where
  K := K
  Wd := R.Wd
  κ := R.κ
  κ₁ := R.κ₁
  V := fun u => (C.M u).V
  ι := fun u => (C.M u).ι
  Vf := fun u => (C.Mf u).V
  ιf := fun u => (C.Mf u).ι
  b' := R.b'
  X' := R.X'
  cc := R.cc
  b := fun u => (C.M u).b
  X := fun u => (C.M u).X
  M := fun u => (C.M u).L
  N0 := C.Nu
  bf := fun u => (C.Mf u).b
  Xf := fun u => (C.Mf u).X
  Mf := fun u => (C.Mf u).L
  σ := C.sgExp
  τ := C.tauExp
  B := R.B
  v := R.v
  Y := R.Y
  Y' := R.Y'
  Ball := R.Ball
  γ := R.γ
  Bf := R.Bf
  Vr := fun u => C.Vr u R.v
  S := C.S
  gain := fun j w => Arith.gainD P.N P.Cs P.Lv (Arith.pOf (Arith.hs w)) (j.1 + 1)
  Fj := fun j w => P.N.FjP (j.1 + 1) (Arith.pOf (Arith.hs w))
  Ej := fun u j w => Arith.E P.N P.Cs P.Lv P.sd (P.code u) (j.1 + 1) (Arith.hs w)
  iop := Arith.io P.N P.Cs
  T := C.T
  h := R.h
  lam := C.lamT
  Dstar := C.Dstar
  η0 := R.η0
  η1 := R.η1
  e0 := R.e0

def ColFacts (C : ColObj K I) : Prop := ∃ J : ColIface K I, J.toColObj = C

structure PlaceDataCompatible (C : ColObj K I) (P : PlDat K I) : Prop where
  f : C.f = P.N.R.f
  k : C.k = P.N.R.k
  m : C.m = P.N.R.m
  sd : Arith.SdOk P.N P.sd
  code : ∀ u, P.code u ∈ P.Lv.Ws
  T : ∀ u, C.T u = P.Lv.T (P.code u)
  overPi : ∀ u w, prW w = C.T u → (C.overPi u w ↔ 0 < vAdd w (Arith.elt P.sd (P.Lv.piT (P.code u))))
  supp : C.supp = Arith.supp P.N P.Lv K
  tau : C.tau = fun w => Arith.tau P.N P.Cs (Arith.pOf w)
  sg : ∀ u, C.sg u = Arith.sg P.N P.Cs P.Lv P.sd (P.code u)

structure Service (C : ColObj K I) (P : PlDat K I) : Prop where
  len : ∀ u, ∀ w ∈ C.supp, prW w ≠ C.T u →
    ((C.lenMN u w : ℚ) : ℝ) ≤ (C.dM u : ℝ) * (Arith.tau P.N P.Cs (Arith.pOf w) + Arith.io P.N P.Cs (Arith.pOf w))

structure PlSizes (C : ColObj K I) (P : PlDat K I) (bb : ℝ) : Prop where
  Ta : ∑ w ∈ C.supp, Arith.sz w (Arith.tau P.N P.Cs (Arith.pOf w)) ≤ bb ^ 2
  level : ∀ u, 4 * (C.f : ℝ) / (C.T u : ℝ) * bb ^ 2
    + (C.f : ℝ) * Real.log ((C.T u : ℝ) - 1) / ((C.T u : ℝ) - 2) ≤ 1

structure RowHyp [Fintype I] (C : ColObj K I) (R : RowArg C) (sg : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  what₂ : 0 < Fintype.card R.κ
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  sg_pos : 0 < sg
  sg_le : sg ≤ 1 / 20
  proviso : C.Dstar / sg ≤ ∑ u, (Fintype.card (C.Mf u).ι : ℝ)
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ sg / 2
  η1_le : R.η1 ≤ sg / 2
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ sg / 2
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0

end Fam

structure Pt (I : Type) where
  K : Type
  [i1 : Field K]
  [i2 : NumberField K]
  [i3 : StarRing K]
  [i4 : IsTotallyComplex K]
  C : ColObj K I
  P : PlDat K I
  R : RowArg C

attribute [instance] Pt.i1 Pt.i2 Pt.i3 Pt.i4

def Pt.fam {I : Type} (m : ℕ) (Q : Pt I) : LChain2.Fam I m := famC m Q.C Q.P Q.R

structure Pt.Ok {I : Type} (Q : Pt I) (m f : ℕ) (bb : ℝ) : Prop where
  m : Q.P.N.R.m = m
  f : Q.C.f = f
  facts : ColFacts Q.C
  tied : PlaceDataCompatible Q.C Q.P
  cst : Q.P.Cs.admitted
  service : Service Q.C Q.P
  sizes : PlSizes Q.C Q.P bb
  above : ∀ δ ∈ Q.P.Lv.Ws, Q.P.N.sc.X'' Q.P.N.R.n < (Q.P.Lv.T δ : ℝ)

end Formalism.L2.GlobalTheoryTheory.FamCol

end
