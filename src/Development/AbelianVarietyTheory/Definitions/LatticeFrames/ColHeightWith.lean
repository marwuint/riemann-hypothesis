import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.HarderNarasimhan.QuotRealize

noncomputable section

namespace GlobalTheory.CoreHt

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
  (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def phiCol {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : I.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst I u m2 b} (A : ChKer W Ch sel mu cst I P u m2 b hY)
    (hF : ∀ j, (chF W sel mu I u j).Ok) {G : ChGlob X R.m} (hL : I.Ok Ch sel mu cst G m2) :
    (MramH W Ch hX u).V →ₗ[X.K] Module.Dual X.K (MtildeH W Ch hX sel mu P).V :=
  (PtilE W Ch sel mu P (mtildeOk W Ch sel mu hX P) u) ∘ₗ (colC A hF hL) ∘ₗ (MramV W Ch u).subtype

end Col

end GlobalTheory.CoreHt
