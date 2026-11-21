import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

section General

variable (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def retie (O : OnObj S P oc) (ι : Bs.J → ℕ) : OnObj S P oc :=
  { O with
    E := fun v j => EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) (depOf T EX Tp hK) v (ι j)
    σ := fun _ j => sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
    nnK := fun j => nnKAt (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
    T := Tp.TO
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := D.R.k
    m := D.R.m
    f := D.R.f
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Bs.J => WeightAlgebra.DF (lR Tp hK (ι j)) : ℕ) : ℝ) }

variable {T EX Tp hK} {O : OnObj S P oc} {ι : Bs.J → ℕ}

theorem b_eq (h : RunTie T EX Tp hK O ι) : O.b = L.sc.b := by
  unfold OnObj.b OnObj.xe Scale.b Scale.L
  rw [h.x_eq, h.eps_eq]

end General

theorem numOf_aPlus (L : SizeData₂ D) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (numOf D L).aPlus j z i = DV.aPlusQ D j (plOf D z) i := rfl

theorem numOf_aMinus (L : SizeData₂ D) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (numOf D L).aMinus j z i = DV.aMinusQ D j (plOf D z) i := rfl

end GlobalTheory.RunDepth.Model
