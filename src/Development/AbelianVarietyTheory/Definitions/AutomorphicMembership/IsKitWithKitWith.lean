import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PadTrueNormDetConst
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

variable {D : D7}

abbrev StFams (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), StFam S κ

section One

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (F : StFam S κ) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D)

abbrev PolOf {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

abbrev padWith {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (cts : Ats S κ) {jC : JC D} (hj : jC.Pinned) (hA : AdmEx S κ) :
    PadPkg D N j s.Comp jC ngTrue :=
  padTrue s Φ (metsOf x Φ) jC hj hA (locStOf F cts) (globStOf F cts)

structure IsKitWith (k : KitT s L jC) (d : s.Comp → D.what₂.Tau → ℝ) (x : ToroidalCompactificationData s) (P : PolOf x k.Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : Prop where
  ats : cts.Over jC
  bd : IsBdOf x L k.B
  fl : k.fl = flBetti s k.Φ L
  mb : k.Mb = mbarOf P
  pad : k.pad = padWith F x k.Φ cts hj hA
  deg : d = degFlat s k.Φ (metsOf x k.Φ)

namespace IsKitWith

end IsKitWith

end One

def IsKitOf (st : StFams D) : KitClass D := fun A N j S κ s L jC k d =>
  ∃ x P cts hj hA, IsKitWith (st A N j S κ) s L jC k d x P cts hj hA

namespace IsKitOf

end IsKitOf

end GlobalTheory.ShFam
