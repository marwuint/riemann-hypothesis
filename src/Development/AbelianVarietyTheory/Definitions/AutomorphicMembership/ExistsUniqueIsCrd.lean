import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TieModel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
  (P : LevFam X.E X.K R.r Pr.vGs)

def frm (y : Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) :
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Forms :=
  (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
    (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y)

theorem isFormOf_unique {V : Type} {y : V} {x x' : MtildeV W Ch sel mu P} (h : IsFormOf W Ch sel mu hX P x y)
    (h' : IsFormOf W Ch sel mu hX P x' y) : x = x' := by
  obtain ⟨F, hF, e, rfl⟩ := h
  obtain ⟨F', hF', e', rfl⟩ := h'
  have := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).injective (eq_of_heq (e.trans e'.symm))
  subst this
  rfl

end Forms

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)

end Cols

section Standard

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links

end Standard

end GlobalTheory.Mem.Top.Bl.TieModel

end
