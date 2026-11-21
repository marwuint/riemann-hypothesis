import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
import Development.AutomorphicArithmetic.ConductorsKronecker.Imports
import Development.AutomorphicArithmetic.ConductorsKronecker.kronecker
import Development.AutomorphicArithmetic.ConductorsKronecker.InertiaD
import Development.AutomorphicArithmetic.ConductorsKronecker.IsInertIff
import Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace Formalism.L2.GlobalTheoryTheory.Arith

abbrev baseOf (D : D7) (L : SizeData₂ D) : Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

section Rfl

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p j : ℕ) (t0 : G.HH D)

theorem rho_eq : G.rho D K L.sc = (baseOf D L).rho K := rfl

end Rfl

namespace Loc

end Loc

abbrev datumOf (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) : NumDatum where
  R := D.R
  sc := L.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := Del
  h0 := h0
  hc := fun z => D.hc (tauPl D z)

structure InstanceCompatible {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Ce : ℝ) (Del h0 : ℕ) : Prop where
  del : D.s.Del = (Del : ℚ)
  eta : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)
  bs : ∀ h t, X.bs h t = bsH h t
  ep : G.EpDef X Ce
  kap : G.KapIDef X K
  fills : ∀ j ∈ SizeData₂.lifts D, ∀ z, G.fill X (G.bL L) j z = wPl D j z

open Classical in

structure LevelCompatible {D : D7} {L : SizeData₂ D} {Del h0 : ℕ} (EX : ErrX D) (Lv : Lev (datumOf D L Del h0)) (sd : D.what₂.LL) :
    Prop where
  ws : Lv.Ws = Finset.univ.image (fun u : D.what₂.Word => (D.s.letter u : Code (datumOf D L Del h0)))
  T : ∀ u, Lv.T (D.s.letter u) = (D.mem u).A.T
  sdOk : SdOk (datumOf D L Del h0) sd
  piT : ∀ u τ, tauLL D τ (EX.piT u : D.host.E) = elt sd (Lv.piT (D.s.letter u))
  piG : ∀ i τ, tauPib EX i τ = eltBar sd (Lv.piG i)
  DGam : (D.mem D.u₀).C.DGam = Lv.DGam

section Family

variable {eps : ℝ} (Fm : FamP eps)

variable {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x)

structure NewTies (Del h0 : ℕ) (Lv : Lev (datumOf (Fm.D x i) (Fm.L x i) Del h0)) (sd : (Fm.D x i).what₂.LL) : Prop where
  del : (Fm.D x i).s.Del = (Del : ℚ)
  eta : (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (h0 : ℝ)
  bs : ∀ h t, (Fm.Gx x i).bs h t = bsH h t
  lev : LevelCompatible (Fm.ex x hx i).errX Lv sd

variable {Del h0 : ℕ} {Lv : Lev (datumOf (Fm.D x i) (Fm.L x i) Del h0)} {sd : (Fm.D x i).what₂.LL}
  (hN : NewTies Fm hx i Del h0 Lv sd)

include hN

end Family

end Formalism.L2.GlobalTheoryTheory.Arith

end
