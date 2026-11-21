import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ThetaFrameCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Scalars

variable {X Y : Scheme.{0}}

theorem resG_resG {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

def mulSec {L : LB X} (a : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top a * s.f i
  compat i j := by
    rw [map_mul, map_mul, s.compat i j]
    exact (congrArg (· * _) ((resG_resG _ _ a).trans (resG_resG _ _ a).symm)).trans (mul_left_comm _ _ _)

end Scalars

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def scalSec {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) : LB.Sec (PPx x) :=
  mulSec ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a)) s

theorem scalSec_f {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) (i : (PPx x).ι) :
    (scalSec x a s).f i = scal x a i * s.f i := rfl

variable {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G : SAB H (Sp T.V)}

variable {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Point

end GlobalTheory.ThetaFrameCompare
