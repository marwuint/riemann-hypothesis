import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

def zetaLogDeriv {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (logDeriv (fun s => riemannZeta s * DirichletCharacter.LFunction χ s) 0).re

def maxLift (D : D7) (g : ℕ → ℝ) : ℝ :=
  (Icc 1 D.R.m).sup' ⟨1, mem_Icc.2 ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩⟩ g

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

def pageOf : SlopeBoundParameters where
  Pl := D.what₂.Tau
  fPl := inferInstance
  x := L.sc.x
  eps := L.sc.eps
  rd := D.host.rdE
  v := D.host.v
  dN := D.host.d
  dimNeZero := ⟨D.host.hyp.2.1.ne_zero⟩
  χ := chiK D
  Z := haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩; zetaLogDeriv (chiK D)
  logOmK := eulerConstantTerm D.host.d
  logOm := L.logOm
  f := D.R.f
  m := D.R.m
  k := D.R.k
  S := L.Sc
  η := L.etaSz
  R := (D.R.r : ℝ) / 2
  PPp := maxLift D fun j => (numAt Q j).PPp
  PPpp := maxLift D fun j => (numAt Q j).PPpp
  PP := Q.PP
  PPT := Real.sqrt (ppTsq Q)
  Zpg := zBase L
  nV := D.R.nV
  Nr := D.R.r
  g12 := (D.host.g 0 : ℝ) * D.host.g 1

theorem pageOf_L : (pageOf Q).L = L.sc.L := rfl

theorem pageOf_b : (pageOf Q).b = L.sc.b := rfl

theorem pageOf_lrd : (pageOf Q).lrd = lrd D := rfl

theorem log_derivative_at_zero : (pageOf Q).L0 = dlogL D 0 := rfl

theorem leafDiff_pageOf : LeafDiff (pageOf Q) := rfl

section Weights

variable (D) in

def uMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uAn D j τ i - (cTw D j : ℤ) * deW D j i

variable (D) in

def kapMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - (cTw D j : ℤ) * deW D j i

variable (D) in

def twW (j : ℕ) (_ : D.what₂.Tau) (i : ℕ) : ℤ := (cTw D j : ℤ) * deW D j i

def remW (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  aW D j τ i - aW D j τ (D.R.k - 2) - ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ) * uOne Q j τ i

def uTwo (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uOne Q j τ i + remW Q j τ i

def uCan (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := canW D j i + uTwo Q j τ i + (placeRankTwoOne.dimY D : ℤ) * uOne Q j τ i

def uTop (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uCan Q j τ i + (tN Q : ℤ) * uOne Q j τ i

end Weights

section Numbers

def nOneW (j : ℕ) : ℝ := ∑ τ, nrm D (uOne Q j τ)

def nPrW (j : ℕ) : ℝ := ∑ τ, nrm D (uPr Q j τ)

def supPrW (j : ℕ) : ℕ := univ.sup fun τ : D.what₂.Tau => (range D.R.r).sup fun i => (uPr Q j τ i).natAbs

def bZero (j : ℕ) : ℝ := 4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (1 + (supPrW Q j : ℝ) / (LevelStarExponents.h0 L / (4 * tR Q)))

variable (D L) in

def badPrimes (B : ℝ) : Finset ℕ :=
  (range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (discr D.host.E).natAbs * levDeep D L).primeFactors

variable (D) in

def diff_vp (p : ℕ) : ℝ := (padicValNat p (discr D.host.E).natAbs : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

def aSum (j : ℕ) : ℝ :=
  ∑ p ∈ badPrimes D L (bZero Q j), (1 / ((p : ℝ) - 1) + 40 * diff_vp D p) * (nPrW Q j + (numAt Q j).Pa) * Real.log p

def cInf (j : ℕ) : ℝ := (nOneW Q j + 6 * (numAt Q j).Pinf) / 2

def cA (j : ℕ) : ℝ := 26 * (26 * dY D ^ 2 + 2 * zed Q j * tR Q)

def lZero (j : ℕ) : ℝ := (numAt Q j).PPp * (nKap D j / tR Q + 1) + (numAt Q j).al

def cJ (C2 : ℝ) (j : ℕ) : ℝ :=
  dY D * (numAt Q j).PPp * (nKap D j / tR Q + 1) + tR Q * ((numAt Q j).QJ + (numAt Q j).PPp) +
    (dY D + 3) * addY C2 (pageOf Q) / tR Q

def cG (j : ℕ) : ℝ := (dY D + 1) * ((numAt Q j).o + (numAt Q j).B7 + 1) / 2 + 1

def rOne (C2 : ℝ) (j : ℕ) : ℝ :=
  cJ Q C2 j + 26 * dY D ^ 2 * (lZero Q j + Real.log (tR Q)) + (tR Q + dY D + 1) * (numAt Q j).Bt +
    (tR Q + dY D ^ 2) * (cG Q j + 2)

def rTwo (j : ℕ) : ℝ :=
  tR Q * (Real.log 2 + lZero Q j + (numAt Q j).Bt / 2) + 2 * ((numAt Q j).PPp * nKap D j)

def lamKap (j : ℕ) : ℝ := (numAt Q j).G * (nKap D j - (D.R.f : ℝ) * D.R.r * D.R.nV / 2 + D.R.nV)

variable (D L) in

def measureMove : ℝ := 61 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L

end Numbers

section Transport

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open Formalism.L2.Pj hiding kap

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

open Classical in

def toWt (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : Weight Dw :=
  fun τ i => ∑ t, if τ.1 = DV.tauEmb D t then v t i else 0

variable {Dw : Datum H}

def psiOf {T : Par D} (h : T.PinHost) (t : D.what₂.Tau) : Psi T.H := ⟨DV.tauEmb D t, h.2.2.2 t⟩

theorem psiOf_bijective {T : Par D} (h : T.Pins) : Function.Bijective (psiOf h.1) := by
  have hj : InR D 1 := ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩
  refine ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => ?_⟩
  obtain ⟨t, ht⟩ := ((GlobalTheory.WeightExponents.weight_exponents D T h 1 hj
    (WeightAlgebra.wscalar D 1 0 Even.zero)).2.2.1 τ.1).1 τ.2
  exact ⟨t, Subtype.ext ht.symm⟩

variable {T : Par D} {j : ℕ}

theorem sig_eq (h : T.Pins) (hj : InR D j) :
    (T.Dw j).p = pp D j ∧ (T.Dw j).q = qq D j ∧ (T.Dw j).p + (T.Dw j).q = D.R.r := by
  obtain ⟨h1, h2, -⟩ := h.2.2.2 j hj
  refine ⟨h1, h2, ?_⟩
  have := D.R.m_add_three_le_k
  have := hj.1
  have := hj.2
  rw [h1, h2]
  simp only [Ranks.sigW, Ranks.r]; omega

theorem dimFlag_eq (h : T.Pins) (hj : InR D j) : dimFlag (T.Dw j) = placeRankTwoOne.dimY D := by
  rw [dimFlag, Formalism.DegreeFormula.dimFl, (sig_eq h hj).2.2, ← Fintype.card_of_bijective (psiOf_bijective h), D.what₂.card_Tau,
    placeRankTwoOne.dimY, Nat.choose_two_right]

variable (D) in

def thetaExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) ((D.R.nV / 2 : ℕ) : ℤ)

variable (D) in

def plainExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) 0

end Transport

end GlobalTheory.SlopeRec
