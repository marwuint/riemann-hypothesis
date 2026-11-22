import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.Points GlobalTheory.CovTest

namespace GlobalTheory.VdmRec

section Free

variable {k : Type} [CommRing k] {X : Scheme.{0}} {ι : Type} [Fintype ι]

abbrev clo (z : X) : Closeds X := ⟨closure {z}, isClosed_closure⟩

instance isIntegral_clo (z : X) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
  isIntegral_red (Z := clo z) isIrreducible_singleton.closure

structure FlagSp (E : X.Modules) (r : ℕ) : Type 1 where

  Y : Scheme.{0}

  π : Y ⟶ X

  fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r
  univ : IsFlagBundle π (fun _ : Unit => E) (fun _ => r) (fun _ => fl)

end Free

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal
open GlobalTheory.LieVB (omega unitSec dUnit)

def IsDualEig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (G : ∀ σ', EigMet Z σ') {g : ℕ} (h : VMetric Z.s (omega Z.t.G) g) : Prop :=
  ∀ (σ' : c.F →+* ℂ) (yc : CxPts (genStr Z) σ') (y : CxPts Z.s (σ'.comp β)), y.1 = yc.1 ≫ genι Z →
    ∀ (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W)
      (f f' : Γ(Z.t.G.left, W)), y ∈ ptsIn Z.s (σ'.comp β) U →
      (h.met (σ'.comp β)).form (dUnit Z.t.G hU f) (dUnit Z.t.G hU f') y =
        ∑ τ : E →+* ℂ, HermFrame.form ((G σ').gram yc u τ)⁻¹ (fun i => (valR (u.v τ i) W f).snd)
          fun i => (valR (u.v τ i) W f').snd

structure DRBase {D : D7} (O : Setup D) (c : O.s.Comp) : Type 1 where

  x : ToroidalCompactificationData O.s

  P : PolOf x O.Φ
  core : O.CoreWith x P

  B : Scheme.{0}
  [int : IsIntegral B]

  b : B ⟶ O.s.T.Z.X
  [cl : IsClosedImmersion b]
  gen : b (genericPoint B) = genι O.s.T.Z ((O.Φ.C c).π (genericPoint (O.Φ.C c).Y.X))
  ar : IsArithVar (b ≫ O.s.T.Z.s) (dimGr D.what₂.Tau O.N O.j)

  h : ℝ → VMetric O.s.T.Z.s (omega O.s.T.Z.t.G) (D.R.f * O.N)
  H : ∀ R, (h R).IsCInf
  dual : ∀ R, IsDualEig (fun σ' => x.eigMetAt σ' (some R)) (h R)

  F : FlagSp ((Scheme.Modules.pullback b).obj (omega O.s.T.Z.t.G)) (D.R.f * O.N)

namespace DRBase

attribute [instance] int cl

variable {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c)

instance : IsLocallyNoetherian M.B := M.ar.isLocallyNoetherian

abbrev q : M.B ⟶ Sp (𝓞 O.κ.c.F) := M.b ≫ O.s.T.Z.s

def lam (R : ℝ) : HermLB M.q := VMetric.det ((M.H R).pull M.b rfl)

def lamB : LB M.B := VB.det ((Scheme.Modules.pullback M.b).obj (omega O.s.T.Z.t.G)) (D.R.f * O.N)

def bd : Set M.B := {w | M.b w ∉ abLocus O.s.T.Z.t.G}

structure Emb : Type where

  a : ℕ
  a_pos : 0 < a

  n : ℕ

  f : M.B ⟶ PSpace (𝓞 O.κ.c.F) n
  f_str : f ≫ PSpace.str _ n = M.q
  iso : LBIso ((ProjSpace.hermitianTwistingSheaf (𝓞 O.κ.c.F) n).B.pull f) (lbPow M.lamB a)

variable {M} in

def Emb.Good (I : M.Emb) (z : M.B) (e : ℕ) : Prop :=
  topologicalKrullDim (closure ({z} : Set M.B)) = (e + 2 : ℕ) ∧
    topologicalKrullDim (I.f '' (closure {z} ∩ M.bd)) + 3 ≤ (e + 2 : ℕ) ∧ (CharZero (M.B.residueField z) → z ∉ M.bd)

end DRBase

end GlobalTheory.VdmRec

end
